module StaticLists

using Base: front, tail, isdone
using Static

export KeyedStaticList, StaticList, slist

@static if isdefined(Base, Symbol("@assume_effects"))
    using Base: @assume_effects
else
    macro assume_effects(_, ex)
        Base.@pure ex
    end
end

struct Nil end

const nil = Nil()

# decomposes into a block of symbols up to the `N`th position
# ntails_expr(3) ->
# quote
#    x1 = Base.tail(x0)
#    x2 = Base.tail(x1)
#    x3 = Base.tail(x2)
# end
function ntails_expr(N::Int)
    out = Expr(:block, Expr(:meta, :inline))
    psym = :x0
    for i in 1:N
        push!(out.args, Expr(:(=), Symbol(:x, i), :(Base.tail($psym))))
        psym = Symbol(:x, i)
    end
    out
end

"""
    StaticList(items...)

A statically-sized, singly-linked StaticList.
"""
struct StaticList{F,T,L}
    first::F
    tail::T
    length::L
end

function StaticList(@nospecialize(f), @nospecialize(t::StaticList))
    StaticList(f, t, slength(t) + static(1))
end
StaticList(@nospecialize(x::StaticList)) = x
StaticList(@nospecialize(x::Tuple)) = _tuple_to_StaticList(StaticInt{nfields(x)}(), x)
@generated function _tuple_to_StaticList(::StaticInt{N}, @nospecialize(t::Tuple)) where {N}
    e = :($(slist()))
    for i in N:-1:1
        e = Expr(:call, :StaticList, :(@inbounds(getfield(t, $i))), e)
    end
    return e
end
const EmptyList = StaticList{Nil,Nil,StaticInt{0}}

Base.reverse(@nospecialize(x::StaticList)) = _reverse(x, slength(x))
@generated function _reverse(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :($(slist()))
    for i in 0:(N - 1)
        out = :(StaticList(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

# takes the first `N` values and attaches them to the new root/tail
@generated function _reroot_chunk(
    @nospecialize(x0::StaticList),
    @nospecialize(root::StaticList),
    ::StaticInt{N}
) where {N}
    blk = ntails_expr(N)
    out = :(root)
    for i in (N - 1):-1:0
        out = :(StaticList(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

@inline function _reroot_chunk(@nospecialize(x0::StaticList), @nospecialize(root::StaticList), N::Int)
    if N === 1
        return StaticList(first(x0), root)
    else
        return StaticList(first(x0), _reroot_chunk(tail(x), root, N - 1))
    end
end


include("slist.jl")

struct NFirst{P,L}
    parent::P
    length::L
end
Base.parent(@nospecialize x::NFirst) = getfield(x, :parent)

const OneItem = Union{StaticList{T where T,EmptyList,StaticInt{1}}, NFirst{P where P,StaticInt{1}}}

const KeylessList = Union{StaticList,NFirst}

"""
    KeyedStaticList(items::Pair...)
    KeyedStaticList(keys::StaticList, values::StaticList)

An instance of [`StaticList`](@ref) with keys for each element.
"""
struct KeyedStaticList{K,V}
    keys::K
    values::V

    function KeyedStaticList(@nospecialize(k::KeylessList), @nospecialize(v::KeylessList))
        length(k) === length(v) || throw(ArgumentError("keys and values are of different length"))
        new{typeof(k),typeof(v)}(k, v)
    end
end
KeyedStaticList(@nospecialize(x::Pair)) = KeyedStaticList(slist(x[1]), slist(x[2]))
KeyedStaticList(@nospecialize(x::Pair), @nospecialize(xs::Pair...)) = pushfirst(KeyedStaticList(xs...), x)
@inline function KeyedStaticList(; @nospecialize(kwargs...))
    v = values(kwargs)
    KeyedStaticList(StaticList(static(keys(v))), StaticList(values(v)))
end

const ListType = Union{KeylessList,KeyedStaticList}

"""
    slist(args...)

Composes a list where each argument is a member of the list.
"""
@inline slist() = StaticList(nil, nil, StaticInt{0}())
@inline slist(@nospecialize(x), @nospecialize(args...)) = StaticList(x, StaticList(args))

@generated function _eltype(::StaticInt{N}, @nospecialize(T::Type{<:StaticList})) where {N}
    if N === 1
        return :(T.parameters[1])
    else
        out = :(T.parameters[1])
        t = :(T.parameters[2])
        for _ in 1:(N-1)
            out = Expr(:call, :typejoin, out, :($(t).parameters[1]))
            t = :($(t).parameters[2])
        end
        return out
    end
end

@assume_effects :total function _known_instance(T::DataType)
    if isdefined(T, :instance)
        return getfield(T, :instance)
    else
        return nothing
    end
end
@inline known_instance(T::DataType) = _known_instance(T)
@inline known_instance(@nospecialize(x)) = _known_instance(typeof(x))

# TODO doc insert
"""
    insert
"""
function insert(
    @nospecialize(x::KeylessList),
    @nospecialize(v),
    @nospecialize(i::Integer)
)
    @boundscheck checkbounds(x, i)
    unsafe_insert(x, v, i)
end
@inline function unsafe_insert(@nospecialize(x::StaticList), @nospecialize(v), i::Int)
    if i === 1
        return StaticList(v, x)
    else
        return StaticList(first(x), unsafe_insert(tail(x), v, i - 1))
    end
end
@generated function unsafe_insert(
    @nospecialize(x::StaticList),
    @nospecialize(v),
    ::StaticInt{N}
) where {N}

    out = ntails_expr(N)
    r = :(StaticList(v, $(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(StaticList(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

"""
    StaticLists.deleteat(StaticList, key)

Returns a `StaticList` without the value corresponding to `key`.

!!! warning
    This is not part of the public API and may change without notice.
"""
deleteat

@generated function unsafe_deleteat(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(Base.tail($(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(StaticList(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

"""
    pushfirst(StaticList, item)

Returns a new StaticList with `item` added to the front.
"""
pushfirst

"""
    push(StaticList, item)

Returns a new StaticList with `item` added to the end.
"""
push(x::EmptyList, item) = StaticList(item, x)
@inline push(x::StaticList, item) = StaticList(first(x), push(tail(x), item))
@inline function push(@nospecialize(x::KeyedStaticList), kv::Pair)
    KeyedStaticList(push(keys(x), getfield(kv, 1)), push(values(x), getfield(kv, 2)))
end

"""
    StaticLists.pop(StaticList) -> (last(StaticList), Base.front(StaticList))

Returns a tuple with the last item and the StaticList without the last item.

!!! warning
    This is not part of the public API and may change without notice.
"""
pop

"""
    StaticLists.popfirst(StaticList) -> (first(StaticList), Base.tail(StaticList))

Returns a tuple with the first item and the StaticList without the first item.

!!! warning
    This is not part of the public API and may change without notice.
"""
popfirst

"""
    StaticLists.popat(StaticList, key) -> (StaticList[key], StaticLists.delete(StaticList, key))

Returns the value at `key` and the StaticList without the value.

!!! warning
    This is not part of the public API and may change without notice.
"""
popat
@generated function unsafe_popat(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(Base.tail($(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(StaticList(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, :(first($(Symbol(:x, N - 1))), $r))
    return out
end


## filter
## findfirst
function Base.findfirst(f::Function, @nospecialize(lst::StaticList))
    n = find_first(f, lst)
    if n === 0
        return nothing
    else
        return n
    end
end
@inline find_first(f, @nospecialize(lst::OneItem)) = f(first(lst)) ? 1 : 0
@inline function find_first(f, @nospecialize(lst::StaticList))
    if f(first(lst))
        return 1
    else
        n = find_first(f, tail(lst))
        if n === 0
            return 0
        else
            return n + 1
        end
    end
end

@inline function maybe_static_find_first(@nospecialize(f), @nospecialize(lst::StaticList))
    if isdefined(typeof(lst), :instance) && isdefined(typeof(f), :instance)
        return static_find_first(f, lst)
    else
        return find_first(f, lst)
    end
end

@generated function static_find_first(::F, ::L) where {F,L}
    :($(StaticInt{find_first(F.instance, L.instance)}()))
end

@generated function _unsafe_getindex(@nospecialize(lst::StaticList), ::StaticInt{N}) where {N}
    e = :lst
    pos = 1
    while pos !== N
        e = :(tail($e))
        pos += 1
    end
    Expr(:block, Expr(:meta, :inline), :(first($e)))
end

@generated function unsafe_setindex(@nospecialize(x0::StaticList), v, ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(StaticList(v, Base.tail($(Symbol(:x, N-1)))))
    for i in (N - 2):-1:0
        r = :(StaticList(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

@generated function _generated_mapfoldl(f, op, @nospecialize(x0::StaticList), init::I, ::StaticInt{N}) where {I,N}
    out = ntails_expr(N)
    if I <: Base._InitialValue
        e = :(f(first($(Symbol(:x, 0)))))
        idx = 1
    else
        e = :init
        idx = 0
    end
    for i in idx:(N - 1)
        e = :(op($(e), f(first($(Symbol(:x, i))))))
    end
    push!(out.args, e)
    return out
end

@generated function _generated_mapfoldr(f, op, @nospecialize(x0::StaticList), init::I, ::StaticInt{N}) where {I,N}
    out = ntails_expr(N)
    if I <: Base._InitialValue
        e = :(f(first($(Symbol(:x, N - 1)))))
        idx = N - 2
    else
        e = :init
        idx = N - 1
    end

    for i in idx:-1:0
        xsym = Symbol(:x, i)
        e = :(op(f(first($xsym)), $(e)))
    end
    push!(out.args, e)
    return out
end


# TODO map(::KeyedStaticList)
@nospecialize

Base.eltype(x::ListType) = eltype(typeof(x))
Base.eltype(::Type{EmptyList}) = Union{}
Base.eltype(T::Type{<:StaticList}) = _eltype(slength(T), T)
Base.eltype(T::Type{<:KeyedStaticList}) = Pair{keytype(T),valtype(T)}

Base.valtype(x::ListType) = valtype(typeof(x))
Base.valtype(T::Type{<:KeylessList}) = eltype(T)
Base.valtype(T::Type{<:KeyedStaticList}) = eltype(T.parameters[2])

Base.IteratorSize(T::Type{<:ListType}) = Base.HasLength()

###
# keys
###
Base.keytype(x::ListType) = keytype(typeof(x))
Base.keytype(T::Type{<:KeylessList}) = Int
Base.keytype(T::Type{<:KeyedStaticList}) = eltype(T.parameters[1])

Base.haskey(x::ListType, key) = in(key, keys(x))

@inline Base.eachindex(x::StaticList) = Base.OneTo(length(x))
@inline Base.keys(x::StaticList) = eachindex(x)
Base.keys(x::KeyedStaticList) = getfield(x, :keys)

###
# Indexing
###
Base.getindex(lst::KeylessList, ::Colon) = collect(lst)
Base.collect(x::StaticList) = x
Base.collect(x::NFirst) = _reroot_chunk(parent(x), slist(), slength(x))
Base.collect(x::KeyedStaticList) = KeyedStaticList(collect(keys(x)), collect(values(x)))

function Base.getindex(lst::KeyedStaticList, i)
    out = get(lst, i, nil)
    @boundscheck out === nil && throw(BoundsError(lst, i))
    return out
end
@inline function Base.getindex(lst::KeylessList, i::Integer)
    @boundscheck checkbounds(lst, i)
    _unsafe_getindex(lst, i)
end
# TODO Base.getindex(lst::KeylessList, i::AbstractUnitRange)
_unsafe_getindex(x::NFirst, i::Integer) = _unsafe_getindex(parent(x), i)
@inline function _unsafe_getindex(@nospecialize(lst::StaticList), i::Int)
    i === 1 ? first(lst) : _unsafe_getindex(tail(lst), i - 1)
end

function Base.setindex(x::ListType, v, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_setindex(x, v, i)
end
@inline function unsafe_setindex(x::StaticList, v, i::Int)
    if i === 1
        return StaticList(v, tail(x))
    else
        return StaticList(first(x), unsafe_setindex(tail(x), v, i - 1))
    end
end
function Base.setindex(kl::KeyedStaticList, v, key)
    vs = Base.setindex(values(kl), v, maybe_static_find_first(==(key), keys(kl)))
    KeyedStaticList(keys(kl), vs)
end

@inline function Base.get(lst::KeylessList, i::Integer, d)
    checkbounds(Bool, lst, i) ? _unsafe_getindex(lst, i) : d
end
# TODO benchmark and test this thing
@inline function Base.get(kl::KeyedStaticList, key, d)
    get(values(kl), maybe_static_find_first(==(key), keys(kl)), d)
end

###
# immutable mutators
###
function deleteat(lst::StaticList, i::Integer)
    @boundscheck checkbounds(lst, i)
    unsafe_deleteat(lst, i)
end
@inline function unsafe_deleteat(lst::StaticList, i::Int)
    if i === 1
        return tail(lst)
    else
        return StaticList(first(lst), unsafe_deleteat(tail(lst), i - 1))
    end
end
function deleteat(kl::KeyedStaticList, key)
    i = find_first(==(key), keys(kl))
    @boundscheck i != 0 || throw(BoundsError(kl, key))
    KeyedStaticList(unsafe_deleteat(keys(kl), i), unsafe_deleteat(values(kl), i))
end


pushfirst(x::StaticList, item) = StaticList(item, x)
@inline function pushfirst(x::KeyedStaticList, kv::Pair)
    KeyedStaticList(pushfirst(keys(x), getfield(kv, 1)), pushfirst(values(x), getfield(kv, 2)))
end


@inline pop(x::StaticList) = popat(x, slength(x))
@inline function pop(kl::KeyedStaticList)
    k, kt = pop(keys(kl))
    v, vt = pop(values(kl))
    Pair(k, v), KeyedStaticList(kt ,vt)
end

@inline popfirst(x::StaticList) = first(x), tail(x)
@inline function popfirst(kl::KeyedStaticList)
    kf, kt = popfirst(keys(kl))
    vf, vt = popfirst(values(kl))
    Pair(kf, vf), KeyedStaticList(kt ,vt)
end

function popat(lst::StaticList, i::Integer)
    @boundscheck checkbounds(lst, i)
    unsafe_popat(lst, i)
end
@inline function unsafe_popat(x::StaticList, i::Int)
    if i === 1
        return first(x), tail(x)
    else
        f, t = unsafe_popat(tail(x), i - 1)
        return f, StaticList(first(x), t)
    end
end

###
# Comparison
###
Base.:(==)(::EmptyList, ::EmptyList) = true
function Base.:(==)(x::ListType, y::ListType)
    if length(x) === length(y)
        itrx = iterate(x)
        itry = iterate(y)
        while itrx !== nothing
            itrx[1] == itry[1] || return false
            itrx = iterate(x, itrx[2])
            itry = iterate(y, itry[2])
        end
        return true
    else
        return false
    end
end

@inline function Base.in(x, lst::KeylessList)
    for i in lst
        i == x && return true
    end
    return false
end

@inline Base.isempty(x::ListType) = length(x) === 0

Base.empty(x::StaticList) = slist()
Base.empty(x::KeyedStaticList) = KeyedStaticList(empty(keys(x)), empty(values(x)))

slength(T::DataType) = T.parameters[3]()
slength(x::KeylessList) = getfield(x, :length)
slength(x::KeyedStaticList) = slength(keys(x))
@inline Base.length(x::KeylessList) = Int(slength(x))
@inline Base.length(x::KeyedStaticList) = length(keys(x))

###
# Base.front / Base.tail
###
function Base.tail(::EmptyList)
    throw(ArgumentError("Cannot call Base.tail on an empty StaticList"))
end
Base.tail(::OneItem) = slist()
Base.tail(x::StaticList) = getfield(x, :tail)
Base.tail(x::NFirst) = (len = slength(x); NFirst(tail(parent(x)), len - one(len)))
@inline Base.tail(x::KeyedStaticList) = KeyedStaticList(tail(keys(x)), tail(values(x)))

@noinline function Base.front(::EmptyList)
    throw(ArgumentError("Cannot call Base.front on an empty StaticList"))
end
@inline Base.front(::OneItem) = slist()
@inline Base.front(x::StaticList) = NFirst(x, slength(x) - static(1))
@inline Base.front(x::NFirst) = NFirst(parent(x), slength(x) - static(1))
# FIXME this should be able to handle different types of lists
@inline function Base.front(x::KeyedStaticList)
    KeyedStaticList(front(keys(x)), front(values(x)))
end

@noinline function Base.first(::EmptyList)
    throw(ArgumentError("Attempt to access first element of empty StaticList."))
end
Base.first(x::StaticList) = getfield(x, :first)
function Base.first(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    return NFirst(x, i)
end
function Base.first(x::NFirst, i::Integer)
    @boundscheck checkbounds(x, i)
    return NFirst(parent(x), i)
end
@inline Base.first(x::KeyedStaticList) = Pair(first(keys(x)), first(values(x)))

@noinline function Base.last(::EmptyList)
    throw(ArgumentError("Attempt to access last element of empty StaticList."))
end
Base.last(x::StaticList) = @inbounds x[slength(x)]
@inline Base.last(x::KeyedStaticList) = Pair(last(keys(x)), last(values(x)))
function Base.last(x::KeylessList, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_last(x, i)
end
@inline function unsafe_last(x::StaticList, i::Integer)
    if i == length(x)
        return x
    else
        return unsafe_last(tail(x), i)
    end
end
unsafe_last(x::NFirst, i::Integer) = NFirst(unsafe_last(parent(x), i), slength(x) - i)

Base.values(x::StaticList) = x
Base.values(x::KeyedStaticList) = getfield(x, :values)

Base.checkbounds(x::KeylessList, i) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
Base.checkbounds(::Type{Bool}, x::KeylessList, i::Integer) = 1 <= i <= slength(x)
function Base.checkbounds(::Type{Bool}, x::KeylessList, i::AbstractUnitRange)
    checkbounds(Bool, x, first(x)) && checkbounds(Bool, x, last(x))
end

Base.isdone(x::StaticList, s::StaticList) = isempty(s)
Base.isdone(x::KeyedStaticList, s) = isempty(getfield(s, 1))

Base.iterate(::EmptyList) = nothing
Base.iterate(lst::StaticList) = first(lst), tail(lst)
@inline function Base.iterate(x::StaticList, state)
    if Base.isdone(x, state)
        return nothing
    else
        return first(state), tail(state)
    end
end
@inline function Base.iterate(x::KeyedStaticList, s= (keys(x), values(x)))
    if Base.isdone(x, s)
        return nothing
    else
        return Pair(first(getfield(s, 1)), first(getfield(s, 2))), (tail(getfield(s, 1)), tail(getfield(s, 2)))
    end
end
@inline function Base.iterate(x::NFirst, s=(parent(x), length(x)))
    len = getfield(s, 2)
    if len === 0
        return nothing
    else
        lst = getfield(s, 1)
        return first(lst), (tail(lst), len - 1)
    end
end

###
# Mapping/Reducing
###
Base.filter(f, ::EmptyList) = slist()
@inline function Base.filter(f, lst::StaticList)
    fst = first(lst)
    if f(fst)
        return StaticList(fst, filter(f, tail(lst)))
    else
        return filter(f, tail(lst))
    end
end

Base.map(f, x::EmptyList) = x
@inline Base.map(f, lst::StaticList) = mapfoldr(f, StaticList, lst, init=slist())

@inline function Base.mapfoldl(f, op, x::StaticList; init=Base._InitialValue())
    _generated_mapfoldl(f, op, x::StaticList, init, slength(x))
end
@inline function Base.mapfoldr(f, op, x::StaticList; init=Base._InitialValue())
    _generated_mapfoldr(f, op, x, init, slength(x))
end

Base.show(io::IO, x::ListType) = show(io, MIME"text/plain"(), x)
Base.show(io::IO, ::MIME"text/plain", ::Nil) = print(out, "nil")
@noinline function Base.show(io::IO, m::MIME"text/plain", x::StaticList)
    print(io, "slist(" * str_list(x) * ")")
end
@noinline function Base.show(io::IO, m::MIME"text/plain", x::NFirst)
    print(io, "NFirst(" * str_list(x) * ")")
end
@noinline function Base.show(io::IO, m::MIME"text/plain", x::KeyedStaticList)
    print(io, "KeyedStaticList(" * str_list(x) * ")")
end
@noinline function str_list(x)
    str = ""
    N = length(x)
    i = 1
    for x_i in x
        str *= "$(x_i)"
        if N !== i
            str *= ", "
        end
        i += 1
    end
    return str
end

@specialize

end

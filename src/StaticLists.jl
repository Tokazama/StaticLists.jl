module StaticLists

using Base: front, tail, isdone
using Static

export KeyedStaticList, StaticList, list

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

const EmptyList = StaticList{Nil,Nil,StaticInt{0}}
const OneItem{T} = StaticList{T,EmptyList,StaticInt{1}}
const TwoItems{T1,T2} = StaticList{T1,OneItem{T2},StaticInt{2}}
const ThreeItems{T1,T2,T3} = StaticList{T1,TwoItems{T2,T3},StaticInt{3}}
const FourItems{T1,T2,T3,T4} = StaticList{T1,ThreeItems{T2,T3,T4},StaticInt{4}}

const none = StaticList(nil, nil, StaticInt(0))

@generated function _reverse(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :none
    for i in 0:(N - 1)
        out = :(cons(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

# takes the first `N` values and attaches them to the new root/tail
@generated function _reroot_chunk(@nospecialize(x0::StaticList), @nospecialize(r::StaticList), ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :(r)
    for i in (N - 1):-1:0
        out = :(cons(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

@inline function _reroot_chunk(@nospecialize(x0::StaticList), @nospecialize(root::StaticList), N::Int)
    if N === 1
        return cons(first(x0), root)
    else
        return cons(first(x0), _reroot_chunk(tail(x), root, N - 1))
    end
end

@generated function _genmap(@nospecialize(f), @nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :none
    for i in (N - 1):-1:0
        out = :(cons(f(first($(Symbol(:x, i)))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

"""
    KeyedStaticList(items::Pair...)
    KeyedStaticList(keys::StaticList, values::StaticList)

An instance of [`StaticList`](@ref) with keys for each element.
"""
struct KeyedStaticList{K,V}
    keys::K
    values::V

    function KeyedStaticList(@nospecialize(k::StaticList), @nospecialize(v::StaticList))
        length(k) === length(v) || throw(ArgumentError("keys and values are of different length"))
        new{typeof(k),typeof(v)}(k, v)
    end
end
KeyedStaticList(@nospecialize(x::Pair)) = KeyedStaticList(list(x[1]), list(x[2]))
KeyedStaticList(@nospecialize(x::Pair), @nospecialize(xs::Pair...)) = pushfirst(KeyedStaticList(xs...), x)

const ListType = Union{StaticList,KeyedStaticList}

"""
    list(args...)

Composes a list where each argument is a member of the list.
"""
list

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
function insert(@nospecialize(x::StaticList), @nospecialize(v), @nospecialize(i::Integer))
    @boundscheck checkbounds(x, i)
    unsafe_insert(x, v, i)
end
@inline function unsafe_insert(@nospecialize(x::StaticList), @nospecialize(v), i::Int)
    if i === 1
        return cons(v, x)
    else
        return cons(first(x), unsafe_insert(tail(x), v, i - 1))
    end
end
@generated function unsafe_insert(@nospecialize(x::StaticList), @nospecialize(v), ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(cons(v, $(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
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
        r = :(cons(first($(Symbol(:x, i))), $r))
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
push(x::EmptyList, item) = cons(item, x)
@inline push(x::StaticList, item) = cons(first(x), push(tail(x), item))
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
        r = :(cons(first($(Symbol(:x, i))), $r))
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

@generated function unsafe_getindex(@nospecialize(lst::StaticList), ::StaticInt{N}) where {N}
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
    r = :(cons(v, Base.tail($(Symbol(:x, N-1)))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
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

@inline cons(x, y) = cons(x, StaticList(x, none, StaticInt(1)))
@inline cons(x, ::EmptyList) = StaticList(x, none, StaticInt(1))
@inline cons(x, y::OneItem) = StaticList(x, y, StaticInt(2))
@inline cons(x, y::TwoItems) = StaticList(x, y, StaticInt(3))
@inline cons(x, y::ThreeItems) = StaticList(x, y, StaticInt(4))
@inline cons(x, y::FourItems) = StaticList(x, y, StaticInt(5))
@inline cons(x, y::StaticList) = StaticList(x, y, StaticInt(1) + slength(y))

list() = none
@inline list(x, args...) = cons(x, list(args...))

Base.eltype(x::ListType) = eltype(typeof(x))
Base.eltype(::Type{EmptyList}) = Union{}
Base.eltype(T::Type{<:StaticList}) = _eltype(slength(T), T)
Base.eltype(T::Type{<:KeyedStaticList}) = Pair{keytype(T),valtype(T)}

Base.valtype(x::ListType) = valtype(typeof(x))
Base.valtype(T::Type{<:StaticList}) = eltype(T)
Base.valtype(T::Type{<:KeyedStaticList}) = eltype(T.parameters[2])

Base.IteratorSize(T::Type{<:ListType}) = Base.HasLength()

###
# keys
###
Base.keytype(x::ListType) = keytype(typeof(x))
Base.keytype(T::Type{<:StaticList}) = Int
Base.keytype(T::Type{<:KeyedStaticList}) = eltype(T.parameters[1])

Base.haskey(x::ListType, key) = in(key, keys(x))

@inline Base.eachindex(x::StaticList) = Base.OneTo(length(x))
@inline Base.keys(x::StaticList) = eachindex(x)
Base.keys(x::KeyedStaticList) = getfield(x, :keys)


Base.reverse(x::Union{EmptyList,OneItem}) = x
Base.reverse(x::StaticList) = _reverse(x, slength(x))

###
# Indexing
###
Base.getindex(x::StaticList, ::Colon) = x
Base.collect(x::StaticList) = x
Base.collect(x::KeyedStaticList) = KeyedStaticList(collect(keys(x)), collect(values(x)))

function Base.getindex(lst::KeyedStaticList, i)
    out = get(lst, i, nil)
    @boundscheck out === nil && throw(BoundsError(lst, i))
    return out
end
@inline function Base.getindex(lst::StaticList, i::Integer)
    @boundscheck checkbounds(lst, i)
    unsafe_getindex(lst, i)
end
# TODO Base.getindex(lst::StaticList, i::AbstractUnitRange)
unsafe_getindex(lst::OneItem, ::Int) = first(lst)
@inline unsafe_getindex(lst::TwoItems, i::Int) = i === 1 ? first(lst) : last(lst)
@inline function unsafe_getindex(lst::StaticList, i::Int)
    i === 1 ? first(lst) : unsafe_getindex(tail(lst), i - 1)
end

function Base.setindex(x::StaticInt, v, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_setindex(x, v, i)
end
@inline unsafe_setindex(x::OneItem, v, i::Int) = cons(v, none)
@inline function unsafe_setindex(x::TwoItems, v, i::Int)
    i === 1 ? cons(v, tail(x)) : cons(first(x), v)
end
@inline function unsafe_setindex(x::StaticList, v, i::Int)
    i === 1 ? cons(v, tail(x)) : cons(first(x), unsafe_setindex(tail(x), v, i - 1))
end
function Base.setindex(kl::KeyedStaticList, v, key)
    vs = Base.setindex(values(kl), v, maybe_static_find_first(==(key), keys(kl)))
    KeyedStaticList(keys(kl), vs)
end

@inline function Base.get(lst::StaticList, i::Integer, d)
    checkbounds(Bool, lst, i) ? unsafe_getindex(lst, i) : d
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
unsafe_deleteat(::OneItem, i::Int) = none
@inline unsafe_deleteat(x::TwoItems, i::Int) = i === 1 ? tail(x) : cons(first(x), none)
@inline function unsafe_deleteat(lst::StaticList, i::Int)
    if i === 1
        return tail(lst)
    else
        return cons(first(lst), unsafe_deleteat(tail(lst), i - 1))
    end
end
function deleteat(kl::KeyedStaticList, key)
    i = find_first(==(key), keys(kl))
    @boundscheck i != 0 || throw(BoundsError(kl, key))
    KeyedStaticList(unsafe_deleteat(keys(kl), i), unsafe_deleteat(values(kl), i))
end

@inline pushfirst(x::StaticList, item) = cons(item, x)
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
@inline unsafe_popat(x::OneItem, i::Int) = first(x), none
@inline function unsafe_popat(x::TwoItems, i::Int)
    if i === 1
        return first(x), tail(x)
    else
        return last(x), cons(first(x), none)
    end
end
@inline function unsafe_popat(x::StaticList, i::Int)
    if i === 1
        return first(x), tail(x)
    else
        f, t = unsafe_popat(tail(x), i - 1)
        return f, cons(first(x), t)
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

@inline function Base.in(x, lst::StaticList)
    for i in lst
        i == x && return true
    end
    return false
end

@inline Base.isempty(x::ListType) = length(x) === 0

Base.empty(x::StaticList) = none
Base.empty(x::KeyedStaticList) = KeyedStaticList(empty(keys(x)), empty(values(x)))

slength(T::DataType) = T.parameters[3]()
slength(x::StaticList) = getfield(x, :length)
slength(x::KeyedStaticList) = slength(keys(x))
@inline Base.length(x::StaticList) = Int(slength(x))
@inline Base.length(x::KeyedStaticList) = length(keys(x))

###
# Base.front / Base.tail
###
function Base.tail(::EmptyList)
    throw(ArgumentError("Cannot call Base.tail on an empty StaticList"))
end
Base.tail(::OneItem) = none
Base.tail(x::StaticList) = getfield(x, :tail)
@inline Base.tail(x::KeyedStaticList) = KeyedStaticList(tail(keys(x)), tail(values(x)))

@noinline function Base.front(::EmptyList)
    throw(ArgumentError("Cannot call Base.front on an empty StaticList"))
end
@inline Base.front(::OneItem) = none
@inline Base.front(x::StaticList) = first(x, slength(x) - static(1))
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
    _reroot_chunk(x, none, i)
end
@inline Base.first(x::KeyedStaticList) = Pair(first(keys(x)), first(values(x)))

@noinline function Base.last(::EmptyList)
    throw(ArgumentError("Attempt to access last element of empty StaticList."))
end
Base.last(x::StaticList) = @inbounds x[slength(x)]
@inline Base.last(x::KeyedStaticList) = Pair(last(keys(x)), last(values(x)))
function Base.last(x::StaticList, i::Integer)
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

Base.values(x::StaticList) = x
Base.values(x::KeyedStaticList) = getfield(x, :values)

Base.checkbounds(x::StaticList, i) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
Base.checkbounds(::Type{Bool}, x::StaticList, i::Integer) = 1 <= i <= slength(x)
function Base.checkbounds(::Type{Bool}, x::StaticList, i::AbstractUnitRange)
    checkbounds(Bool, x, first(x)) && checkbounds(Bool, x, last(x))
end

Base.isdone(x::StaticList, s::StaticList) = isempty(s)
Base.isdone(x::KeyedStaticList, s) = isempty(getfield(s, 1))

Base.iterate(::EmptyList) = nothing
Base.iterate(lst::StaticList) = first(lst), tail(lst)
@inline function Base.iterate(x::StaticList, state)
    if isdone(x, state)
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
###
# Mapping/Reducing
###
Base.filter(f, ::EmptyList) = none
@inline function Base.filter(f, lst::StaticList)
    fst = first(lst)
    if f(fst)
        return cons(fst, filter(f, tail(lst)))
    else
        return filter(f, tail(lst))
    end
end

Base.map(f, x::EmptyList) = x
@inline Base.map(f, x::StaticList) = _genmap(f, x, slength(x))

@inline function Base.mapfoldl(f, op, x::StaticList; init=Base._InitialValue())
    _generated_mapfoldl(f, op, x::StaticList, init, slength(x))
end
@inline function Base.mapfoldr(f, op, x::StaticList; init=Base._InitialValue())
    _generated_mapfoldr(f, op, x, init, slength(x))
end

Base.show(io::IO, x::ListType) = show(io, MIME"text/plain"(), x)
Base.show(io::IO, ::MIME"text/plain", ::Nil) = print(out, "nil")
@noinline function Base.show(io::IO, m::MIME"text/plain", x::StaticList)
    print(io, "list(" * str_list(x) * ")")
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

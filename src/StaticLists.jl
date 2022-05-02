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
function list_expr(N::Int)
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

    StaticList() = new{Nil,Nil,StaticInt{0}}()
    function StaticList(@nospecialize(f), @nospecialize(t::StaticList), @nospecialize(l::StaticInt))
        new{typeof(f),typeof(t),typeof(l)}(f, t, l)
    end
    function StaticList(@nospecialize(f), @nospecialize(t::StaticList))
        StaticList(f, t, slength(t) + static(1))
    end
end

StaticList(@nospecialize(x::StaticList)) = x
StaticList(@nospecialize(x::Tuple)) = _tuple_to_StaticList(StaticInt{nfields(x)}(), x)
@generated function _tuple_to_StaticList(::StaticInt{N}, @nospecialize(t::Tuple)) where {N}
    e = :EMPTY_StaticList
    for i in N:-1:1
        e = Expr(:call, :StaticList, :(@inbounds(getfield(t, $i))), e)
    end
    return e
end
const EmptyList = StaticList{Nil,Nil,StaticInt{0}}
const EMPTY_StaticList = StaticList()
const OneItem{T} = StaticList{T,EmptyList,StaticInt{1}}

struct MaskedList
end

# TODO document
"""
    slist(args...)
"""
slist(@nospecialize(args...)) = StaticList(args)

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
KeyedStaticList(@nospecialize(x::Pair)) = KeyedStaticList(slist(x[1]), slist(x[2]))
KeyedStaticList(@nospecialize(x::Pair), @nospecialize(xs::Pair...)) = pushfirst(KeyedStaticList(xs...), x)
@inline function KeyedStaticList(; @nospecialize(kwargs...))
    v = values(kwargs)
    KeyedStaticList(StaticList(static(keys(v))), StaticList(values(v)))
end

const ListType = Union{StaticList,KeyedStaticList}

Base.haskey(@nospecialize(kl::ListType), key) = in(key, keys(kl))

Base.eltype(@nospecialize x::ListType) = eltype(typeof(x))
Base.eltype(::Type{EmptyList}) = Union{}
Base.eltype(@nospecialize T::Type{<:StaticList}) = _eltype(slength(T), T)
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
Base.eltype(@nospecialize(T::Type{<:KeyedStaticList})) = Pair{keytype(T),valtype(T)}

@assume_effects :total function _known_instance(T::DataType)
    if isdefined(T, :instance)
        return getfield(T, :instance)
    else
        return nothing
    end
end
@inline known_instance(T::DataType) = _known_instance(T)
@inline known_instance(@nospecialize(x)) = _known_instance(typeof(x))

Base.keytype(@nospecialize(x::ListType)) = keytype(typeof(x))
Base.keytype(@nospecialize(T::Type{<:ListType})) = eltype(T.parameters[1])

Base.valtype(@nospecialize(x::ListType)) = valtype(typeof(x))
Base.valtype(@nospecialize(T::Type{<:StaticList})) = eltype(T)
Base.valtype(@nospecialize(T::Type{<:KeyedStaticList})) = eltype(T.parameters[2])

Base.front(::EmptyList) = throw(ArgumentError("Cannot call Base.front on an empty StaticList"))
Base.front(@nospecialize(lst::OneItem)) = EMPTY_StaticList
@inline Base.front(@nospecialize(lst::StaticList)) = StaticList(first(lst), front(tail(lst)))
Base.front(@nospecialize(kl::KeyedStaticList)) = KeyedStaticList(front(keys(kl)), front(values(kl)))

Base.IteratorSize(@nospecialize(T::Type{<:ListType})) = Base.HasLength()

Base.:(==)(::EmptyList, ::EmptyList) = true
Base.:(==)(::EmptyList, @nospecialize(y::StaticList)) = false
Base.:(==)(@nospecialize(x::StaticList), ::EmptyList) = false
@inline function Base.:(==)(@nospecialize(x::StaticList),@nospecialize(y::StaticList))
    if first(x) == first(y)
        return ==(tail(x), tail(y))
    else
        return false
    end
end
function Base.:(==)(@nospecialize(x::KeyedStaticList),@nospecialize(y::KeyedStaticList))
    ==(keys(x), keys(y)) && ==(values(x), values(y))
end

function insert(@nospecialize(x::StaticList), v, @nospecialize(i::Integer))
    @boundscheck (1 <= i && i <= length(i) + 1) || throw(BoundsError(x, i))
    unsafe_insert(x, v, i)
end

@generated function unsafe_insert(@nospecialize(x::StaticList), v, ::StaticInt{N}) where {N}
    out = list_expr(N)
    r = :(StaticList(v, $(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(StaticList(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

@inline function unsafe_insert(@nospecialize(x::StaticList), v, i::Int)
    if i === 1
        return StaticList(v, x)
    else
        return StaticList(first(x), unsafe_insert(tail(x), v, i - 1))
    end
end

"""
    StaticLists.deleteat(StaticList, key)

Returns a `StaticList` without the value corresponding to `key`.

!!! warning
    This is not part of the public API and may change without notice.
"""
function deleteat(@nospecialize(lst::StaticList), i)
    @boundscheck checkbounds(lst, i)
    unsafe_deleteat(lst, i)
end
@inline function unsafe_deleteat(@nospecialize(lst::StaticList), i::Int)
    if i === 1
        return tail(lst)
    else
        return StaticList(first(lst), unsafe_deleteat(tail(lst), i - 1))
    end
end
function deleteat(@nospecialize(kl::KeyedStaticList), key)
    i = find_first(==(key), keys(kl))
    @boundscheck i != 0 || throw(BoundsError(kl, key))
    KeyedStaticList(unsafe_deleteat(keys(kl), i), unsafe_deleteat(values(kl), i))
end
@generated function unsafe_deleteat(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    out = list_expr(N)
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
pushfirst(@nospecialize(x::StaticList), item) = StaticList(item, x)
@inline function pushfirst(@nospecialize(x::KeyedStaticList), kv::Pair)
    KeyedStaticList(pushfirst(keys(x), getfield(kv, 1)), pushfirst(values(x), getfield(kv, 2)))
end

"""
    push(StaticList, item)

Returns a new StaticList with `item` added to the end.
"""
push(x::EmptyList, item) = StaticList(item, x)
@inline push(@nospecialize(x::StaticList), item) = StaticList(first(x), push(tail(x), item))
@inline function push(@nospecialize(x::KeyedStaticList), kv::Pair)
    KeyedStaticList(push(keys(x), getfield(kv, 1)), push(values(x), getfield(kv, 2)))
end

"""
    StaticLists.pop(StaticList) -> (last(StaticList), Base.front(StaticList))

Returns a tuple with the last item and the StaticList without the last item.

!!! warning
    This is not part of the public API and may change without notice.
"""
@inline pop(@nospecialize x::StaticList) = popat(x, slength(x))
@inline function pop(@nospecialize(kl::KeyedStaticList))
    k, kt = pop(keys(kl))
    v, vt = pop(values(kl))
    Pair(k, v), KeyedStaticList(kt ,vt)
end

"""
    StaticLists.popfirst(StaticList) -> (first(StaticList), Base.tail(StaticList))

Returns a tuple with the first item and the StaticList without the first item.

!!! warning
    This is not part of the public API and may change without notice.
"""
@inline popfirst(@nospecialize(x::StaticList)) = first(x), tail(x)
@inline function popfirst(@nospecialize(kl::KeyedStaticList))
    kf, kt = popfirst(keys(kl))
    vf, vt = popfirst(values(kl))
    Pair(kf, vf), KeyedStaticList(kt ,vt)
end

"""
    StaticLists.popat(StaticList, key) -> (StaticList[key], StaticLists.delete(StaticList, key))

Returns the value at `key` and the StaticList without the value.

!!! warning
    This is not part of the public API and may change without notice.
"""
function popat(@nospecialize(lst::StaticList), @nospecialize(i::Integer))
    @boundscheck checkbounds(lst, i)
    unsafe_popat(lst, i)
end
@inline function unsafe_popat(@nospecialize(x::StaticList), i::Int)
    if i === 1
        return first(x), tail(x)
    else
        f, t = unsafe_popat(tail(x), i - 1)
        return f, StaticList(first(x), t)
    end
end
@generated function unsafe_popat(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    out = list_expr(N)
    r = :(Base.tail($(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(StaticList(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, :(first($(Symbol(:x, N - 1))), $r))
    return out
end

## filter
Base.filter(f, ::EmptyList) = EMPTY_StaticList
@inline function Base.filter(f, @nospecialize(lst::StaticList))
    fst = first(lst)
    if f(fst)
        return StaticList(fst, filter(f, tail(lst)))
    else
        return filter(f, tail(lst))
    end
end

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

## getindex
@inline function Base.getindex(@nospecialize(lst::StaticList), @nospecialize(i::Integer))
    @boundscheck checkbounds(lst, i)
    _unsafe_getindex(lst, i)
end
_unsafe_getindex(::EmptyList, ::Int) = throw(ArgumentError("this point should never be reached"))
@inline function _unsafe_getindex(@nospecialize(lst::StaticList), i::Int)
    if i === 1
        return first(lst)
    else
        return _unsafe_getindex(tail(lst), i - 1)
    end
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

function Base.getindex(@nospecialize(lst::KeyedStaticList), i)
    out = get(lst, i, nil)
    @boundscheck out === nil && throw(BoundsError(lst, i))
    return out
end
function Base.setindex(@nospecialize(kl::KeyedStaticList), v, @nospecialize(key))
    vs = Base.setindex(values(kl), v, maybe_static_find_first(==(key), keys(kl)))
    KeyedStaticList(keys(kl), vs)
end
@generated function unsafe_setindex(@nospecialize(x0::StaticList), v, ::StaticInt{N}) where {N}
    out = list_expr(N)
    r = :(StaticList(v, Base.tail($(Symbol(:x, N-1)))))
    for i in (N - 2):-1:0
        r = :(StaticList(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

## get
@inline function Base.get(@nospecialize(lst::StaticList), @nospecialize(i::Integer), d)
    if checkbounds(Bool, lst, i)
        return _unsafe_getindex(lst, i)
    else
        return d
    end
end

# TODO benchmark and test this thing
@inline function Base.get(@nospecialize(kl::KeyedStaticList), @nospecialize(key), d)
    get(values(kl), maybe_static_find_first(==(key), keys(kl)), d)
end

# TODO map(::KeyedStaticList)
Base.map(f, @nospecialize(lst::OneItem)) = StaticList(f(first(lst)), StaticList())
@inline Base.map(f, @nospecialize(lst::StaticList)) = StaticList(f(first(lst)), map(f, tail(lst)))

@inline function Base.in(x, @nospecialize(lst::StaticList))
    if x == first(lst)
        return true
    else
        t = tail(lst)
        if t === StaticList()
            return false
        else
            return in(x, t)
        end
    end
end

function Base.setindex(@nospecialize(x::StaticList), v, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_setindex(x, v, i)
end
@inline function unsafe_setindex(@nospecialize(x::StaticList), v, i::Int)
    if i === 1
        return StaticList(v, tail(x))
    else
        return StaticList(first(x), unsafe_setindex(tail(x), v, i - 1))
    end
end

@inline Base.isempty(@nospecialize x::ListType) = length(x) === 0

Base.empty(@nospecialize x::StaticList) = StaticList()
Base.empty(@nospecialize x::KeyedStaticList) = KeyedStaticList(empty(keys(x)), empty(values(x)))

slength(T::DataType) = T.parameters[3]()
slength(@nospecialize x::StaticList) = getfield(x, :length)
@inline Base.length(@nospecialize x::StaticList) = Int(slength(x))
@inline Base.length(@nospecialize x::KeyedStaticList) = length(keys(x))

function Base.tail(::EmptyList)
    throw(ArgumentError("Cannot call Base.tail on an empty StaticList"))
end
Base.tail(@nospecialize x::StaticList) = getfield(x, :tail)
@inline Base.tail(@nospecialize x::KeyedStaticList) = KeyedStaticList(tail(keys(x)), tail(values(x)))

@noinline function Base.first(::EmptyList)
    throw(ArgumentError("Attempt to access first element of empty StaticList."))
end
Base.first(@nospecialize x::StaticList) = getfield(x, :first)
@inline Base.first(@nospecialize x::KeyedStaticList) = Pair(first(keys(x)), first(values(x)))

@noinline function Base.last(::EmptyList)
    throw(ArgumentError("Attempt to access last element of empty StaticList."))
end
Base.last(@nospecialize x::StaticList) = @inbounds x[slength(x)]
@inline Base.last(@nospecialize x::KeyedStaticList) = Pair(last(keys(x)), last(values(x)))

@inline Base.eachindex(@nospecialize(x::StaticList)) = Base.OneTo(length(x))
@inline Base.keys(@nospecialize(x::StaticList)) = eachindex(x)
Base.keys(@nospecialize(x::KeyedStaticList)) = getfield(x, :keys)

Base.values(@nospecialize x::StaticList) = x
Base.values(@nospecialize x::KeyedStaticList) = getfield(x, :values)

Base.checkbounds(@nospecialize(x::ListType), @nospecialize(i)) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
Base.checkbounds(::Type{Bool}, @nospecialize(x::ListType), @nospecialize(i::Integer)) = 1 <= i <= length(x)

Base.isdone(@nospecialize(x::StaticList), @nospecialize(s::StaticList)) = isempty(s)
Base.isdone(@nospecialize(x::KeyedStaticList), @nospecialize(s)) = isempty(getfield(s, 1))

Base.iterate(::EmptyList) = nothing
Base.iterate(@nospecialize(lst::StaticList)) = first(lst), tail(lst)
@inline function Base.iterate(@nospecialize(x::StaticList), @nospecialize(state))
    if Base.isdone(x, state)
        return nothing
    else
        return first(state), tail(state)
    end
end
@inline function Base.iterate(@nospecialize(x::KeyedStaticList), @nospecialize(s)= (keys(x), values(x)))
    if Base.isdone(x, s)
        return nothing
    else
        return Pair(first(getfield(s, 1)), first(getfield(s, 2))), (tail(getfield(s, 1)), tail(getfield(s, 2)))
    end
end

Base.show(io::IO, @nospecialize(x::ListType)) = show(io, MIME"text/plain"(), x)
Base.show(io::IO, ::MIME"text/plain", ::Nil) = print(out, "nil")
@noinline function Base.show(io::IO, m::MIME"text/plain", @nospecialize(x::StaticList))
    print(io, "slist(" * str_list(x) * ")")
end
@noinline function Base.show(io::IO, m::MIME"text/plain", @nospecialize(x::KeyedStaticList))
    print(io, "KeyedStaticList(" * str_list(x) * ")")
end
@noinline function str_list(@nospecialize x)
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

end

module StaticLists

using ArrayInterface
using ArrayInterface: known_first, known_length
import ArrayInterface: static_length as slength
using Base: front, tail
using Static

@static if isdefined(Base, Symbol("@assume_effects"))
    using Base: @assume_effects
else
    macro assume_effects(_, ex)
        Base.@pure ex
    end
end

@inline sub1(@nospecialize n::Integer) = n - one(n)

export KeyedStaticList, StaticList

struct Nil end

const nil = Nil()

"""
    StaticList(items...)

A statically-sized, singly-linked StaticList.
"""
struct StaticList{F,T}
    first::F
    tail::T

    global _StaticList(@nospecialize(f), @nospecialize(t)) = new{typeof(f),typeof(t)}(f, t)
end

const EMPTY_StaticList = _StaticList(nil, nil)
const OneItem{T} = StaticList{T,StaticList{Nil,Nil}}

tuple_to_StaticList(@nospecialize(t::Tuple)) = _tuple_to_StaticList(slength(t), t)
@generated function _tuple_to_StaticList(::StaticInt{N}, @nospecialize(t::Tuple)) where {N}
    e = :EMPTY_StaticList
    for i in N:-1:1
        e = Expr(:call, :_StaticList, :(@inbounds(getfield(t, $i))), e)
    end
    return e
end

StaticList() = EMPTY_StaticList
StaticList(@nospecialize(x)) = _StaticList(x, StaticList())
StaticList(@nospecialize(x), @nospecialize(args...)) = _StaticList(x, tuple_to_StaticList(args))

"""
    KeyedStaticList(items::Pair...)
    KeyedStaticList(keys::StaticList, values::StaticList)

An instance of [`StaticList`](@ref) with keys for each element.
"""
struct KeyedStaticList{K,V}
    keys::K
    values::V

    global _KeyedStaticList(@nospecialize(k), @nospecialize(v)) = new{typeof(k),typeof(v)}(k, v)
end
function KeyedStaticList(@nospecialize(x::Pair))
    k, v = x
    _KeyedStaticList(StaticList(k), StaticList(v))
end
KeyedStaticList(@nospecialize(x::Pair), @nospecialize(xs::Pair...)) = pushfirst(KeyedStaticList(xs...), x)
function KeyedStaticList(@nospecialize(k::StaticList), @nospecialize(v::StaticList))
    @assert length(k) === length(v)
    _KeyedStaticList(k, v)
end
@inline function KeyedStaticList(; @nospecialize(kwargs...))
    v = values(kwargs)
    _KeyedStaticList(tuple_to_StaticList(static(keys(v))), tuple_to_StaticList(values(v)))
end

const StaticListType = Union{StaticList,KeyedStaticList}

Base.haskey(@nospecialize(kl::StaticListType), key) = in(key, keys(kl))

Base.eltype(@nospecialize(lst::StaticListType)) = eltype(typeof(lst))
Base.eltype(::Type{StaticList{Nil,Nil}}) = Any
Base.eltype(@nospecialize T::Type{<:StaticList}) = _eltype(slength(T), T)
@generated function _eltype(::StaticInt{N}, @nospecialize(T::Type{<:StaticList})) where {N}
    if N === 1
        return :(first_type(T))
    else
        out = :(first_type(T))
        t = :(tail_type(T))
        for _ in 1:(N-1)
            out = Expr(:call, :typejoin, out, :(first_type($(t))))
            t = :(tail_type($(t)))
        end
        return out
    end
end
Base.eltype(@nospecialize(T::Type{<:KeyedStaticList})) = Pair{keytype(T),valtype(T)}

@assume_effects :total _first_type(T::DataType) = @inbounds(T.parameters[1])
first_type(@nospecialize(lst::StaticListType)) = first_type(typeof(lst))
first_type(@nospecialize(T::Type{<:StaticList})) = _first_type(T)
first_type(@nospecialize(T::Type{<:KeyedStaticList})) = Pair{first_type(keys_type(T)), first_type(values_type(T))}

@assume_effects :total _tail_type(T::DataType) = @inbounds(T.parameters[2])
tail_type(@nospecialize(lst::StaticListType)) = tail_type(typeof(lst))
tail_type(@nospecialize T::Type{<:StaticList}) = _tail_type(T)

@assume_effects :total _keys_type(T::DataType) = @inbounds(T.parameters[1])
@inline keys_type(@nospecialize(x::StaticListType)) = keys_type(typeof(x))
keys_type(@nospecialize(T::Type{<:KeyedStaticList})) = _keys_type(T)
@inline function keys_type(@nospecialize(T::Type{<:StaticList}))
    ArrayInterface.OptionallyStaticUnitRange{StaticInt{1},StaticInt{known_length(T)}}
end

@assume_effects :total _values_type(T::DataType) = @inbounds(T.parameters[2])
@inline values_type(@nospecialize(x::StaticListType)) = values_type(typeof(x))
@inline values_type(@nospecialize(T::Type{<:KeyedStaticList})) = _values_type(T)
values_type(@nospecialize(T::Type{<:StaticList})) = T

@assume_effects :total function _known_instance(T::DataType)
    if isdefined(T, :instance)
        return getfield(T, :instance)
    else
        return nothing
    end
end
@inline known_instance(T::DataType) = _known_instance(T)
@inline known_instance(@nospecialize(x)) = _known_instance(typeof(x))

Base.keytype(@nospecialize(x::StaticListType)) = eltype(keys_type(x))
Base.keytype(@nospecialize(T::Type{<:StaticListType})) = eltype(keys_type(T))

Base.valtype(@nospecialize(x::StaticListType)) = valtype(typeof(x))
Base.valtype(@nospecialize(T::Type{<:StaticList})) = eltype(T)
Base.valtype(@nospecialize(T::Type{<:KeyedStaticList})) = eltype(values_type(T))

Base.eachindex(@nospecialize(lst::StaticList)) = static(1):slength(lst)
@inline Base.keys(@nospecialize lst::StaticList) = eachindex(lst)
Base.keys(@nospecialize kl::KeyedStaticList) = getfield(kl, :keys)

Base.values(@nospecialize lst::StaticList) = lst
Base.values(@nospecialize kl::KeyedStaticList) = getfield(kl, :values)

Base.first(::StaticList{Nil,Nil}) = throw(ArgumentError("Attempt to access first element of empty StaticList."))
Base.first(@nospecialize lst::StaticList) = getfield(lst, :first)
Base.first(@nospecialize kl::KeyedStaticList) = Pair(first(keys(kl)), first(values(kl)))

Base.last(::StaticList{Nil,Nil}) = throw(ArgumentError("Attempt to access last element of empty StaticList."))
Base.last(@nospecialize lst::OneItem) = first(lst)
Base.last(@nospecialize lst::StaticList) = last(tail(lst))
Base.last(@nospecialize kl::KeyedStaticList) = Pair(last(keys(kl)), last(values(kl)))

Base.tail(::StaticList{Nil,Nil}) = throw(ArgumentError("Cannot call Base.tail on an empty StaticList"))
Base.tail(@nospecialize lst::StaticList) = getfield(lst, :tail)
Base.tail(@nospecialize kl::KeyedStaticList) = _KeyedStaticList(tail(keys(kl)), tail(values(kl)))

Base.front(::StaticList{Nil,Nil}) = throw(ArgumentError("Cannot call Base.front on an empty StaticList"))
Base.front(@nospecialize(lst::OneItem)) = EMPTY_StaticList
@inline Base.front(@nospecialize(lst::StaticList)) = _StaticList(first(lst), front(tail(lst)))
Base.front(@nospecialize(kl::KeyedStaticList)) = _KeyedStaticList(front(keys(kl)), front(values(kl)))

Base.isempty(::StaticList{Nil,Nil}) = true
Base.isempty(@nospecialize(lst::StaticList)) = false
Base.isempty(@nospecialize(kl::KeyedStaticList)) = isempty(keys(kl))

Base.empty(@nospecialize(lst::StaticList)) = EMPTY_StaticList
Base.empty(@nospecialize(kl::KeyedStaticList)) = _KeyedStaticList(EMPTY_StaticList, EMPTY_StaticList)

# ArrayInterface.known_length
ArrayInterface.known_length(@nospecialize(lst::StaticListType)) = known_length(typeof(lst))
ArrayInterface.known_length(::Type{StaticList{Nil,Nil}}) = 0
ArrayInterface.known_length(@nospecialize T::Type{<:OneItem}) = 1
# skipping the middle value helps with inference but this only gets us to a length of ~40 
const StaticList2Plus{T1,T2,T3,L} = StaticList{T1,StaticList{T2,StaticList{T3,L}}}
const StaticList4Plus{T1,T2,T3,T4,T5,L} = StaticList2Plus{T1,T2,T3,StaticList{T4,StaticList{T5,L}}}
const StaticList8Plus{T1,T2,T3,T4,T5,T6,T7,T8,T9,L} = StaticList{T1,StaticList{T2,StaticList{T3,StaticList{T4,StaticList{T5,StaticList{T6,StaticList{T7,StaticList{T8,StaticList{T9,L}}}}}}}}}
const StaticList16Plus{T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,T13,T14,T15,T16,T17,L} = StaticList{T1,StaticList{T2,StaticList{T3,StaticList{T4,StaticList{T5,StaticList{T6,StaticList{T7,StaticList{T8,StaticList{T9,StaticList{T10,StaticList{T11,StaticList{T12,StaticList{T13,StaticList{T14,StaticList{T15,StaticList{T16,StaticList{T17,L}}}}}}}}}}}}}}}}}
ArrayInterface.known_length(@nospecialize(T::Type{<:StaticList16Plus}))::Int = known_length(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(T))))))))))))))))) + 16
ArrayInterface.known_length(@nospecialize(T::Type{<:StaticList8Plus}))::Int = known_length(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(tail_type(T))))))))) + 8
ArrayInterface.known_length(@nospecialize(T::Type{<:StaticList4Plus}))::Int = known_length(tail_type(tail_type(tail_type(tail_type(T))))) + 4
ArrayInterface.known_length(@nospecialize(T::Type{<:StaticList2Plus}))::Int = known_length(tail_type(tail_type(T))) + 2
ArrayInterface.known_length(@nospecialize(T::Type{<:StaticList}))::Int = known_length(tail_type(T)) + 1
ArrayInterface.known_length(@nospecialize(T::Type{<:KeyedStaticList})) = known_length(keys_type(T))

# ArrayInterface.known_first
ArrayInterface.known_first(@nospecialize(x::StaticListType)) = known_instance(first_type(x))
ArrayInterface.known_first(@nospecialize(T::Type{<:StaticListType})) = known_instance(first_type(T))

Base.length(::StaticList{Nil,Nil}) = 0
@inline Base.length(@nospecialize(lst::StaticList)) = length(tail(lst)) + 1
Base.length(@nospecialize(kl::KeyedStaticList)) = length(keys(kl))

Base.IteratorSize(@nospecialize(T::Type{<:StaticListType})) = Base.HasLength()

Base.:(==)(::StaticList{Nil,Nil}, ::StaticList{Nil,Nil}) = true
Base.:(==)(::StaticList{Nil,Nil}, @nospecialize(y::StaticList)) = false
Base.:(==)(@nospecialize(x::StaticList), ::StaticList{Nil,Nil}) = false
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

"""
    StaticLists.deleteat(StaticList, key)

Returns a `StaticList` without the value corresponding to `key`.

!!! warning
    This is not part of the public API and may change without notice.
"""
deleteat(::StaticList{Nil,Nil}, key) = throw(ArgumentError("StaticList must be non-empty"))
function deleteat(@nospecialize(lst::StaticList), i)
    @boundscheck 1 <= i <= length(lst) || throw(BoundsError(lst, i))
    unsafe_deleteat(lst, i)
end
@inline function unsafe_deleteat(@nospecialize(lst::StaticList), @nospecialize(i::Integer))
    if isone(i)
        return tail(lst)
    else
        return _StaticList(first(lst), unsafe_deleteat(tail(lst), sub1(i)))
    end
end
function deleteat(@nospecialize(kl::KeyedStaticList), key)
    i = find_first(==(key), keys(kl))
    @boundscheck i != 0 || throw(BoundsError(kl, key))
    _KeyedStaticList(unsafe_deleteat(keys(kl), i), unsafe_deleteat(values(kl), i))
end

"""
    pushfirst(StaticList, item)

Returns a new StaticList with `item` added to the front.
"""
pushfirst(@nospecialize(lst::StaticList), @nospecialize(item)) = _StaticList(item, lst)
@inline function pushfirst(@nospecialize(kl::KeyedStaticList), @nospecialize(kv::Pair))
    k, v = kv
    _KeyedStaticList(pushfirst(keys(kl), k), pushfirst(values(kl), v))
end

"""
    push(StaticList, item)

Returns a new StaticList with `item` added to the end.

"""
push(@nospecialize(lst::OneItem), @nospecialize(item)) = _StaticList(first(lst), StaticList(item))
push(@nospecialize(lst::StaticList), @nospecialize(item)) = _StaticList(first(lst), push(tail(lst), item))
@inline function push(@nospecialize(kl::KeyedStaticList), @nospecialize(kv::Pair))
    k, v = kv
    _KeyedStaticList(push(keys(kl), k), push(values(kl), v))
end

"""
    StaticLists.pop(StaticList) -> (last(StaticList), Base.front(StaticList))

Returns a tuple with the last item and the StaticList without the last item.

!!! warning
    This is not part of the public API and may change without notice.
"""
pop(::StaticList{Nil,Nil}) = throw(ArgumentError("StaticList must be non-empty."))
pop(@nospecialize(lst::OneItem)) = first(lst), tail(lst)
@inline function pop(@nospecialize(lst::StaticList))
    item, t = pop(tail(lst))
    item, _StaticList(first(lst), t)
end
@inline function pop(@nospecialize(kl::KeyedStaticList))
    k, kt = pop(keys(kl))
    v, vt = pop(values(kl))
    Pair(k, v), _KeyedStaticList(kt ,vt)
end

"""
    StaticLists.popfirst(StaticList) -> (first(StaticList), Base.tail(StaticList))

Returns a tuple with the first item and the StaticList without the first item.

!!! warning
    This is not part of the public API and may change without notice.
"""
popfirst(@nospecialize(lst::StaticList)) = first(lst), tail(lst)
@inline function popfirst(@nospecialize(kl::KeyedStaticList))
    kf, kt = popfirst(keys(kl))
    vf, vt = popfirst(values(kl))
    Pair(kf, vf), _KeyedStaticList(kt ,vt)
end

"""
    StaticLists.popat(StaticList, key) -> (StaticList[key], StaticLists.delete(StaticList, key))

Returns the value at `key` and the StaticList without the value.

!!! warning
    This is not part of the public API and may change without notice.
"""
popat(::StaticList{Nil,Nil}, i::Integer) = throw(ArgumentError("StaticList must be non-empty"))
function popat(@nospecialize(lst::StaticList), i::Integer)
    @boundscheck 1 <= i <= length(lst) || throw(BoundsError(lst, i))
    unsafe_popat(lst, i)
end
@inline function unsafe_popat(@nospecialize(x), @nospecialize(i::Integer))
    if isone(i)
        return first(x), tail(x)
    else
        f, t = popat(tail(x), sub1(i))
        return f, _StaticList(first(x), t)
    end
end

## filter
Base.filter(f, ::StaticList{Nil,Nil}) = EMPTY_StaticList
@inline function Base.filter(f, @nospecialize(lst::StaticList))
    fst = first(lst)
    if f(fst)
        return _StaticList(fst, filter(f, tail(lst)))
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
function Base.getindex(@nospecialize(lst::KeyedStaticList), i)
    out = get(lst, i, nil)
    @boundscheck out === nil && throw(BoundsError(lst, i))
    return out
end
function Base.getindex(@nospecialize(lst::StaticList), i::Integer)
    @boundscheck 1 <= i <= length(lst) || throw(BoundsError(lst, i))
    _unsafe_getindex(lst, i)
end
@inline function _unsafe_getindex(@nospecialize(lst::StaticList), @nospecialize(i::Integer))
    if isone(i)
        return first(lst)
    else
        return _unsafe_getindex(tail(lst), sub1(i))
    end
end

function Base.setindex(@nospecialize(kl::KeyedStaticList), v, @nospecialize(key))
    vs = Base.setindex(values(kl), v, maybe_static_find_first(==(key), keys(kl)))
    _KeyedStaticList(keys(kl), vs)
end
function Base.setindex(@nospecialize(x::StaticList), v, @nospecialize(i::Integer))
    @boundscheck 1 <= i <= length(x) || throw(BoundsError(x, i))
    _setindex(x, v, i)
end
@inline function _setindex(@nospecialize(x::StaticList), v, @nospecialize(i::Integer))
    if isone(i)
        return _StaticList(v, tail(x))
    else
        return _StaticList(first(x), _setindex(tail(x), v, sub1(i)))
    end
end

## get
@inline function Base.get(@nospecialize(lst::StaticList), @nospecialize(i::Integer), d)
    if 1 <= i <= length(lst)
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
Base.map(f, @nospecialize(lst::OneItem)) = StaticList(f(first(lst)))
@inline Base.map(f, @nospecialize(lst::StaticList)) = _StaticList(f(first(lst)), map(f, tail(lst)))

@inline function Base.in(x, @nospecialize(lst::StaticList))
    if x == first(lst)
        return true
    else
        t = tail(lst)
        if t === EMPTY_StaticList
            return false
        else
            return in(x, t)
        end
    end
end

# iteration
Base.isdone(@nospecialize(lst::StaticList), @nospecialize(s)) = s === EMPTY_StaticList
Base.isdone(@nospecialize(lst::KeyedStaticList), @nospecialize(s)) = s === (EMPTY_StaticList,EMPTY_StaticList)

Base.iterate(::StaticList{Nil,Nil}) = nothing
Base.iterate(::KeyedStaticList{StaticList{Nil,Nil},StaticList{Nil,Nil}}) = nothing
Base.iterate(@nospecialize(lst::StaticList)) = first(lst), tail(lst)
@inline function Base.iterate(@nospecialize(lst::StaticList), @nospecialize(state))
    if Base.isdone(lst, state)
        return nothing
    else
        return first(state), tail(state)
    end
end
function Base.iterate(@nospecialize(kl::KeyedStaticList))
    k = keys(kl)
    v = values(kl)
    Pair(first(k), first(v)), (tail(k), tail(v))
end
@inline function Base.iterate(@nospecialize(kl::KeyedStaticList), @nospecialize(s))
    if Base.isdone(kl, s)
        return nothing
    else
        k, v = s
        return Pair(first(k), first(v)), (tail(k), tail(v))
    end
end

Base.show(io::IO, @nospecialize(lst::StaticList)) = show(io, MIME"text/plain"(), lst)
function Base.show(io::IO, ::MIME"text/plain", @nospecialize(lst::StaticList))
    out = "StaticList("
    N = length(lst)
    i = 1
    for m_i in lst
        out *= "$(m_i)"
        if N !== i
            out *= ", "
        end
        i += 1
    end
    out *= ")"
    print(io, out)
end
Base.show(io::IO, @nospecialize(kl::KeyedStaticList)) = show(io, MIME"text/plain"(), kl)
function Base.show(io::IO, ::MIME"text/plain", @nospecialize(kl::KeyedStaticList))
    out = "KeyedStaticList("
    N = length(kl)
    i = 1
    for (k,v) in kl
        out *= "$(k) => $(v)"
        if N !== i
            out *= ", "
        end
        i += 1
    end
    out *= ")"
    print(io, out)
end

end

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

export KeyedList, List

struct Nil end

const nil = Nil()

"""
    List(items...)

A statically sized, singly linked list.
"""
struct List{F,T}
    first::F
    tail::T

    global _List(@nospecialize(f), @nospecialize(t)) = new{typeof(f),typeof(t)}(f, t)
end

const EMPTY_LIST = _List(nil, nil)
const OneItem{T} = List{T,List{Nil,Nil}}
const TwoItems{T1,T2} = List{T1,OneItem{T2}}
const List2Plus{T1,T2,T3,L} = List{T1,List{T2,List{T3,L}}}

tuple_to_list(@nospecialize(t::Tuple)) = _tuple_to_list(slength(t), t)
@generated function _tuple_to_list(::StaticInt{N}, @nospecialize(t::Tuple)) where {N}
    e = :EMPTY_LIST
    for i in N:-1:1
        e = Expr(:call, :_List, :(@inbounds(getfield(t, $i))), e)
    end
    return e
end

List() = EMPTY_LIST
List(@nospecialize(x)) = _List(x, List())
List(@nospecialize(x), @nospecialize(args...)) = _List(x, tuple_to_list(args))

"""
    KeyedList(items::Pair...)
    KeyedList(keys::List, values::List)

An instance of [`List`](@ref) with keys for each element.
"""
struct KeyedList{K,V}
    keys::K
    values::V

    global _KeyedList(@nospecialize(k), @nospecialize(v)) = new{typeof(k),typeof(v)}(k, v)
end
function KeyedList(@nospecialize(x::Pair))
    k, v = x
    _KeyedList(List(k), List(v))
end
KeyedList(@nospecialize(x::Pair), @nospecialize(xs::Pair...)) = pushfirst(KeyedList(xs...), x)
function KeyedList(@nospecialize(k::List), @nospecialize(v::List))
    @assert length(k) === length(v)
    _KeyedList(k, v)
end
@inline function KeyedList(; @nospecialize(kwargs...))
    v = values(kwargs)
    _KeyedList(tuple_to_list(static(keys(v))), tuple_to_list(values(v)))
end

Base.haskey(@nospecialize(kl::KeyedList), key) = in(key, keys(kl))

Base.eltype(@nospecialize lst::List) = eltype(typeof(lst))
Base.eltype(::Type{List{Nil,Nil}}) = Any
Base.eltype(@nospecialize T::Type{<:List}) = _eltype(slength(T), T)
@generated function _eltype(::StaticInt{N}, @nospecialize(T::Type{<:List})) where {N}
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

@assume_effects :total _first_type(T::DataType) = @inbounds(T.parameters[1])
first_type(@nospecialize lst::List) = first_type(typeof(lst))
first_type(@nospecialize T::Type{<:List}) = _first_type(T)

@assume_effects :total _tail_type(T::DataType) = @inbounds(T.parameters[2])
tail_type(@nospecialize lst::List) = tail_type(typeof(lst))
tail_type(@nospecialize T::Type{<:List}) = _tail_type(T)

@assume_effects :total _keys_type(T::DataType) = @inbounds(T.parameters[1])
keys_type(@nospecialize kl::KeyedList) = keys_type(typeof(kl))
keys_type(@nospecialize T::Type{<:KeyedList}) = _keys_type(T)

@assume_effects :total _values_type(T::DataType) = @inbounds(T.parameters[2])
values_type(@nospecialize kl::KeyedList) = values_type(typeof(kl))
values_type(@nospecialize T::Type{<:KeyedList}) = _values_type(T)

Base.eltype(@nospecialize kl::KeyedList) = eltype(typeof(kl))
Base.eltype(@nospecialize T::Type{<:KeyedList}) = Pair{keytype(T),valtype(T)}

Base.keytype(@nospecialize kl::KeyedList) = eltype(keys_type(kl))
Base.keytype(@nospecialize T::Type{<:KeyedList}) = eltype(keys_type(T))

Base.valtype(@nospecialize kl::KeyedList) = eltype(values_type(kl))
Base.valtype(@nospecialize T::Type{<:KeyedList}) = eltype(values_type(T))

Base.eachindex(@nospecialize(lst::List)) = static(1):slength(lst)
@inline Base.keys(@nospecialize lst::List) = eachindex(lst)
Base.keys(@nospecialize kl::KeyedList) = getfield(kl, :keys)

Base.values(@nospecialize lst::List) = lst
Base.values(@nospecialize kl::KeyedList) = getfield(kl, :values)

Base.first(::List{Nil,Nil}) = throw(ArgumentError("Attempt to access first element of empty list."))
Base.first(@nospecialize lst::List) = getfield(lst, :first)
Base.first(@nospecialize kl::KeyedList) = Pair(first(keys(kl)), first(values(kl)))

Base.last(::List{Nil,Nil}) = throw(ArgumentError("Attempt to access last element of empty list."))
Base.last(@nospecialize lst::OneItem) = first(lst)
Base.last(@nospecialize lst::List) = last(tail(lst))
Base.last(@nospecialize kl::KeyedList) = Pair(last(keys(kl)), last(values(kl)))

Base.tail(::List{Nil,Nil}) = throw(ArgumentError("Cannot call Base.tail on an empty list"))
Base.tail(@nospecialize lst::List) = getfield(lst, :tail)
Base.tail(@nospecialize kl::KeyedList) = _KeyedList(tail(keys(kl)), tail(values(kl)))

Base.front(::List{Nil,Nil}) = throw(ArgumentError("Cannot call Base.front on an empty list"))
Base.front(@nospecialize(lst::OneItem)) = EMPTY_LIST
@inline Base.front(@nospecialize(lst::List)) = _List(first(lst), front(tail(lst)))
Base.front(@nospecialize(kl::KeyedList)) = _KeyedList(front(keys(kl)), front(values(kl)))

Base.isempty(::List{Nil,Nil}) = true
Base.isempty(@nospecialize(lst::List)) = false
Base.isempty(@nospecialize(kl::KeyedList)) = isempty(keys(kl))

Base.empty(@nospecialize(lst::List)) = EMPTY_LIST
Base.empty(@nospecialize(kl::KeyedList)) = _KeyedList(EMPTY_LIST, EMPTY_LIST)

ArrayInterface.known_length(@nospecialize(lst::List)) = known_length(typeof(lst))
ArrayInterface.known_length(::Type{List{Nil,Nil}}) = 0
ArrayInterface.known_length(@nospecialize T::Type{<:OneItem}) = 1
ArrayInterface.known_length(@nospecialize T::Type{<:TwoItems}) = 2
# skipping the middle value helps with inference here
function ArrayInterface.known_length(@nospecialize T::Type{<:List2Plus})
    known_length(tail_type(tail_type(T))) + 2
end
ArrayInterface.known_length(@nospecialize(T::Type{<:List})) = known_length(tail_type(T)) + 1
function ArrayInterface.known_length(@nospecialize(T::Type{<:KeyedList}))
    known_length(keys_type(T))
end

@inline function ArrayInterface.known_first(@nospecialize T::Type{<:List})
    f = first_type(T)
    if isdefined(f, :instance)
        return f.instance
    else
        return nothing
    end
end
@inline function ArrayInterface.known_first(@nospecialize T::Type{<:KeyedList})
    k = ArrayInterface.known_first(keys_type(T))
    v = ArrayInterface.known_first(values_type(T))
    if k === nothing || v === nothing
        return nothing
    else
        return Pair(k, v)
    end
end

Base.length(::List{Nil,Nil}) = 0
@inline Base.length(@nospecialize(lst::List)) = length(tail(lst)) + 1
Base.length(@nospecialize(kl::KeyedList)) = length(keys(kl))

Base.IteratorSize(@nospecialize T::Type{<:List}) = Base.HasLength()
Base.IteratorSize(@nospecialize T::Type{<:KeyedList}) = Base.HasLength()

Base.:(==)(::List{Nil,Nil}, ::List{Nil,Nil}) = true
@inline function Base.:(==)(@nospecialize(x::List),@nospecialize(y::List))
    if first(x) == first(y)
        return ==(tail(x), tail(y))
    else
        return false
    end
end
function Base.:(==)(@nospecialize(x::KeyedList),@nospecialize(y::KeyedList))
    ==(keys(x), keys(y)) && ==(values(x), values(y))
end

# TODO function deleteat(@nospecialize(lst::KeyedList), key) end
deleteat(::List{Nil,Nil}, key) = throw(ArgumentError("list must be non-empty"))
function deleteat(@nospecialize(lst::List), i)
    @boundscheck 1 <= i <= length(lst) || throw(BoundsError(lst, i))
    unsafe_deleteat(lst, i)
end
@inline function unsafe_deleteat(@nospecialize(x), @nospecialize(i::Integer))
    if isone(i)
        return tail(x)
    else
        return _List(first(x), unsafe_deleteat(tail(x), sub1(i)))
    end
end

"""
    StaticLists.pushfirst(list, item)

Returns a new list with `item` added to the front.
"""
pushfirst(@nospecialize(lst::List), @nospecialize(item)) = _List(item, lst)
@inline function pushfirst(@nospecialize(kl::KeyedList), @nospecialize(kv::Pair))
    k, v = kv
    _KeyedList(pushfirst(keys(kl), k), pushfirst(values(kl), v))
end

"""
    StaticLists.push(list, item)

Returns a new list with `item` added to the end.
"""
push(@nospecialize(lst::OneItem), @nospecialize(item)) = _List(first(lst), List(item))
push(@nospecialize(lst::List), @nospecialize(item)) = _List(first(lst), push(tail(lst), item))
@inline function push(@nospecialize(kl::KeyedList), @nospecialize(kv::Pair))
    k, v = kv
    _KeyedList(push(keys(kl), k), push(values(kl), v))
end

"""
    StaticLists.pop(list) -> (last(list), Base.front(list))

Returns a tuple with the last item and the list without the last item.
"""
pop(::List{Nil,Nil}) = error("List must be non-empty.")
pop(@nospecialize(lst::OneItem)) = first(lst), tail(lst)
@inline function pop(@nospecialize(lst::List))
    item, t = pop(tail(lst))
    item, _List(first(lst), t)
end
@inline function pop(@nospecialize(kl::KeyedList))
    k, kt = pop(keys(kl))
    v, vt = pop(values(kl))
    Pair(k, v), _KeyedList(kt ,vt)
end

"""
    StaticLists.popfirst(list) -> (first(list), Base.tail(list))

Returns a tuple with the first item and the list without the first item.
"""
popfirst(@nospecialize(lst::List)) = first(lst), tail(lst)
@inline function popfirst(@nospecialize(kl::KeyedList))
    kf, kt = popfirst(keys(kl))
    vf, vt = popfirst(values(kl))
    Pair(kf, vf), _KeyedList(kt ,vt)
end

"""
    StaticLists.popat(list, key) -> (list[key], StaticLists.delete(list, key))

Returns the value at `key` and the list without the value.
"""
popat(::List{Nil,Nil}) = throw(ArgumentError("list must be non-empty"))
function popat(@nospecialize(lst::List), i::Integer)
    @boundscheck 1 <= i <= length(lst) || throw(BoundsError(lst, i))
    unsafe_popat(lst, i)
end
@inline function unsafe_popat(@nospecialize(x), @nospecialize(i::Integer))
    if isone(i)
        return first(x), tail(x)
    else
        f, t = popat(tail(x), sub1(i))
        return f, _List(first(x), t)
    end
end

## filter
Base.filter(f, ::List{Nil,Nil}) = EMPTY_LIST
@inline function Base.filter(f, @nospecialize(lst::List))
    fst = first(lst)
    if f(fst)
        return _List(fst, filter(f, tail(lst)))
    else
        return filter(f, tail(lst))
    end
end

## findfirst
function Base.findfirst(f::Function, @nospecialize(lst::List))
    n = find_first(f, lst)
    if n === 0
        return nothing
    else
        return n
    end
end
@inline find_first(f, @nospecialize(lst::OneItem)) = f(first(lst)) ? 1 : 0
@inline function find_first(f, @nospecialize(lst::List))
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

@inline function maybe_static_find_first(@nospecialize(f), @nospecialize(lst::List))
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
function Base.getindex(@nospecialize(lst::KeyedList), i)
    out = get(lst, i, nil)
    @boundscheck out === nil && throw(BoundsError(lst, i))
    return out
end
function Base.getindex(@nospecialize(lst::List), i::Integer)
    @boundscheck 1 <= i <= length(lst) || throw(BoundsError(lst, i))
    _unsafe_getindex(lst, i)
end
@inline function _unsafe_getindex(@nospecialize(lst::List), @nospecialize(i::Integer))
    if isone(i)
        return first(lst)
    else
        return _unsafe_getindex(tail(lst), sub1(i))
    end
end

function Base.setindex(@nospecialize(kl::KeyedList), v, @nospecialize(key))
    vs = Base.setindex(values(kl), v, maybe_static_find_first(==(key), keys(kl)))
    _KeyedList(keys(kl), vs)
end
function Base.setindex(@nospecialize(x::List), v, @nospecialize(i::Integer))
    @boundscheck 1 <= i <= length(x) || throw(BoundsError(x, i))
    _setindex(x, v, i)
end
@inline function _setindex(@nospecialize(x::List), v, @nospecialize(i::Integer))
    if isone(i)
        return _List(v, tail(x))
    else
        return _List(first(x), _setindex(tail(x), v, sub1(i)))
    end
end

## get
@inline function Base.get(@nospecialize(lst::List), @nospecialize(i::Integer), d)
    if 1 <= i <= length(lst)
        return _unsafe_getindex(lst, i)
    else
        return d
    end
end

# TODO benchmark and test this thing
@inline function Base.get(@nospecialize(kl::KeyedList), @nospecialize(key), d)
    get(values(kl), maybe_static_find_first(==(key), keys(kl)), d)
end

# TODO map(::KeyedList)
Base.map(f, @nospecialize(lst::OneItem)) = List(f(first(lst)))
@inline Base.map(f, @nospecialize(lst::List)) = _List(f(first(lst)), map(f, tail(lst)))

@inline function Base.in(x, @nospecialize(lst::List))
    if x == first(lst)
        return true
    else
        t = tail(lst)
        if t === EMPTY_LIST
            return false
        else
            return in(x, t)
        end
    end
end

# iteration
Base.isdone(@nospecialize(lst::List), @nospecialize(s)) = s === EMPTY_LIST
Base.isdone(@nospecialize(lst::KeyedList), @nospecialize(s)) = s === (EMPTY_LIST,EMPTY_LIST)

Base.iterate(::List{Nil,Nil}) = nothing
Base.iterate(::KeyedList{List{Nil,Nil},List{Nil,Nil}}) = nothing
Base.iterate(@nospecialize(lst::List)) = first(lst), tail(lst)
@inline function Base.iterate(@nospecialize(lst::List), @nospecialize(state))
    if Base.isdone(lst, state)
        return nothing
    else
        return first(state), tail(state)
    end
end
function Base.iterate(@nospecialize(kl::KeyedList))
    k = keys(kl)
    v = values(kl)
    Pair(first(k), first(v)), (tail(k), tail(v))
end
@inline function Base.iterate(@nospecialize(kl::KeyedList), @nospecialize(s))
    if Base.isdone(kl, s)
        return nothing
    else
        k, v = s
        return Pair(first(k), first(v)), (tail(k), tail(v))
    end
end

Base.show(io::IO, @nospecialize(lst::List)) = show(io, MIME"text/plain"(), lst)
function Base.show(io::IO, ::MIME"text/plain", @nospecialize(lst::List))
    out = "List("
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
Base.show(io::IO, @nospecialize(kl::KeyedList)) = show(io, MIME"text/plain"(), kl)
function Base.show(io::IO, ::MIME"text/plain", @nospecialize(kl::KeyedList))
    out = "KeyedList("
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

module StaticLists

using Base: setindex

export
    ForwardList,
    ReverseList,
    StaticList,
    deleteat,
    insert,
    list,
    rlist

@static if isdefined(Base, Symbol("@assume_effects"))
    using Base: @assume_effects
else
    # we can't support anything but :total if @assume_effects isn't implemented yet
    macro assume_effects(args...)
        any(==(:total), args) ? :(Base.@pure $(last(args))) : $(last(args))
    end
end

@nospecialize

const INIT = Base._InitialValue()

struct SkipPosition end

const skippos = SkipPosition()

@inline maybe_skip(f, x) = f(x) ? x : skippos

struct Nil end

const nil = Nil()

struct ForwardList{F,T}
    first::F
    tail::T

    ForwardList(lst::ForwardList) = lst
    @assume_effects :total function ForwardList(f, t::Union{ForwardList,Nil})
        new{typeof(f),typeof(t)}(f, t)
    end
end

struct ReverseList{F,L}
    front::F
    last::L

    ReverseList(lst::ReverseList) = lst
    @assume_effects :total function ReverseList(f::Union{ReverseList,Nil}, l)
        new{typeof(f),typeof(l)}(f, l)
    end
end

const ReverseItem{I} = ReverseList{Nil,I}
const ForwardItem{I} = ForwardList{I,Nil}
const Item{I} = Union{ReverseItem{I},ForwardItem{I}}

const SList{I,N} = Union{ForwardList{I,N},ReverseList{N,I}}

const StaticList = ForwardList

# define this under nospecialize to avoid adding a new method for every new list definition
@inline function Base.convert(T::Type{<:ForwardList}, lst::ForwardList)
    if lst isa T
        lst
    else
        ForwardList(convert(item_type(T), getitem(lst)), convert(next_type(T), next(lst)))
    end
end
@inline function Base.convert(T::Type{<:ReverseList}, lst::ReverseList)
    if lst isa T
        lst
    else
        ReverseList(convert(next_type(T), next(lst)), convert(item_type(T), getitem(lst)))
    end
end

# don't want to ever specialize on this
Base.values(lst::SList) = lst

Base.IteratorSize(T::Type{<:Union{SList,Nil}}) = Base.HasLength()

# returns the closest data value enclosed in the list type
@assume_effects :total getitem(lst::ReverseList) = getfield(lst, :last)
@assume_effects :total getitem(lst::ForwardList) = getfield(lst, :first)

# returns the type of the closest data value enclosed in the list type
item_type(T::Type{<:ReverseList}) = fieldtype(T, :last)
item_type(T::Type{<:ForwardList}) = fieldtype(T, :first)

# returns the next list, skipping over the immediately enclosed data value
@assume_effects :total next(lst::ReverseList) = getfield(lst, :front)
@assume_effects :total next(lst::ForwardList) = getfield(lst, :tail)

# returns the typeof of the next list, skipping over the immediately enclosed data value
next_type(T::Type{<:ForwardList}) = fieldtype(T, :tail)
next_type(T::Type{<:ReverseList}) = fieldtype(T, :front)

# associate a new item with a list
associate(lst::ReverseList, item) = ReverseList(lst, item)
associate(lst::ReverseList, item, items...) = associate(associate(lst, item), items...)
associate(lst::ForwardList, item) = ForwardList(item, lst)

# replace the immediately enclosed data value
setitem(lst::ReverseList, val) = ReverseList(next(lst), val)
setitem(lst::ForwardList, val) = ForwardList(val, next(lst))

## length
unsafe_length(::Nil) = 0
@assume_effects :nothrow :terminates_globally function unsafe_length(lst::SList)
    1 + unsafe_length(next(lst))
end
Base.length(lst::Union{Nil,SList}) = unsafe_length(lst)

# determines if the list is a single item without iterating through whole list for length
# (this shouldn't be an issue unless the list is too long for constant propagation to work)
is_item(lst::SList) = next(lst) === nil

Base.size(x::Union{SList,Nil}) = (length(x),)

Base.eltype(x::Union{SList,Nil}) = eltype(typeof(x))
Base.eltype(::Type{Nil}) = Union{}
Base.eltype(T::Type{<:SList}) = typejoin(item_type(T), next_type(T))

## first
Base.first(lst::ForwardList) = getitem(lst)
Base.first(lst::ReverseList) = first(next(lst))
Base.first(lst::Item) = getitem(lst)

## last
Base.last(lst::ForwardList) = last(next(lst))
Base.last(lst::ReverseList) = getitem(lst)
Base.last(lst::Item) = getitem(lst)

Base.isempty(::Nil) = true
Base.isempty(lst::SList) = false

Base.empty(lst::SList) = nil

## only
Base.only(lst::Item) = getitem(lst)
@noinline function Base.only(x::Union{SList,Nil})
    throw(ArgumentError("list has multiple elements, must contain exactly 1 element"))
end

# Due to the implementation of bounds-checking and reverse indexing for `ReverseList`,
# verifying arrival at the correct item in a list is a bit different. This method makes it
# so we don't have to
_is_position(lst::ReverseList, i::I) where {I} = iszero(i)
_is_position(lst::ForwardList, i::I) where {I} = isone(i)
function _to_position(lst::ReverseList, i::I) where {I}
    ri = unsafe_length(lst) - i
    (1 <= i && ri <= 0), ri
end
_to_position(lst::ForwardList, i::I) where {I} = (1 <= i && i <= unsafe_length(lst)), i

## get
@inline function Base.get(lst::SList, i::I, d) where {I}
    is_inbounds, index = _to_position(lst, i)
    is_inbounds ?  unsafe_getindex(lst, index) : d
end
function Base.get(f::Union{Type,Function}, lst::SList, i::Number)
    out = get(lst, i, INIT)
    out === INIT ? f() : out
end

## getindex
Base.getindex(lst::Item) = getitem(lst)
Base.getindex(lst::SList, ::Colon) = lst
function Base.getindex(lst::SList, i::Number)
    is_inbounds, index = _to_position(lst, i)
    @boundscheck is_inbounds || throw(BoundsError(lst, i))
    unsafe_getindex(lst, index)
end
@inline function unsafe_getindex(lst::SList, i::Number)
    _is_position(lst, i) ? getitem(lst) : unsafe_getindex(next(lst), i - one(i))
end

## setindex
Base.setindex(lst::Item, item) = setitem(lst, item)
function Base.setindex(lst::SList, item, i::Number)
    is_inbounds, index = _to_position(lst, i)
    @boundscheck is_inbounds || throw(BoundsError(lst, i))
    unsafe_setindex(lst, item, index)
end
@inline function unsafe_setindex(lst::SList, item, i::Number)
    if _is_position(lst, i)
        setitem(lst, item)
    else
        associate(unsafe_setindex(next(lst), item, i - one(i)), getitem(lst))
    end
end

## dissociate
dissociate(lst::SList) = getitem(lst), next(lst)
function dissociate(lst::SList, i::Number)
    is_inbounds, index = _to_position(lst, i)
    @boundscheck is_inbounds || throw(BoundsError(lst, i))
    unsafe_dissociate(lst, index)
end
@inline function unsafe_dissociate(lst::SList, i::Number)
    if _is_position(lst, i)
        return getitem(lst), setitem(lst, item)
    else
        v, n = unsafe_dissociate(next(lst), i - one(i))
        return v, associate(getitem(lst), n)
    end
end

Base.@propagate_inbounds function deleteat(lst::SList, i::Number)
    getfield(dissociate(lst, i), 2)
end

## insert
function insert(lst::ForwardList, i::Number, item)
    @boundscheck 1 <= i <= (unsafe_length(lst) + 1) || throw(BoundsError(lst, i))
    unsafe_insert(lst, i, item)
end
function insert(lst::ReverseList, i::Number, item)
    ri = unsafe_length(lst) - i
    @boundscheck 1 <= i && ri >= -1 || throw(BoundsError(lst, i))
    unsafe_insert(lst, ri, item)
end

## iterate
Base.iterate(::Nil) = nothing
Base.iterate(lst::ForwardList) = getitem(lst), 2
@inline function Base.iterate(lst::ForwardList, state::Int)
    state > unsafe_length(lst) ? nothing : (unsafe_getindex(lst, state), state + 1)
end
Base.iterate(lst::ReverseList) = first(lst), unsafe_length(lst) - 1
@inline function Base.iterate(lst::ReverseList, state::Int)
    state === -1 ? nothing : (unsafe_getindex(lst, state), state - 1)
end
Base.iterate(lst::Item, ::Int) = nothing

"""
    list(args...)

Composes a list where each argument is a member of the list.
"""
list(item) = ForwardList(item, nil)
list(item, items...) = ForwardList(item, list(items...))

rlist(item) = ReverseList(nil, item)
rlist(item, items...) = associate(rlist(item), items...)

## assoc
@inline assoc(::SkipPosition, lst::Union{ForwardList,Nil}) = lst

@noinline Base.show(io::IO, x::Union{SList,Nil}) = show(io, MIME"text/plain"(), x)
Base.show(io::IO, ::MIME"text/plain", ::Nil) = print(io, "list()")
@noinline function Base.show(io::IO, ::MIME"text/plain", lst::SList)
    print(io, lst isa ReverseList ? "rlist(" : "list(", _string_list(lst), ")")
end
_string_list(lst::Item) = repr(getitem(lst))
@noinline _string_list(lst::ReverseList) = _string_list(next(lst)) * ", " * repr(getitem(lst))
@noinline _string_list(lst::ForwardList) = repr(getitem(lst)) * ", " * _string_list(next(lst))

# these don't need to iterate in any particular order
Base.all(f, ::Nil) = true
Base.any(f, ::Nil) = false

Base.allequal(::Nil) = true
Base.allequal(lst::Item) = true

Base.allunique(::Nil) = true
Base.allunique(lst::Item) = true

Base.count(f, ::Nil; init=0) = init

## maximum
@inline function Base.maximum(lst::SList; init=INIT)
    init === INIT ? _maximum(next(lst), getitem(lst)) : _maximum(lst, init)
end
@inline _maximum(lst::SList, item) = _maximum(next(lst), max(getitem(lst), item))
_maximum(::Nil, item) = item
_maximum(f, ::Nil, item) = item

## minimum
@inline function Base.minimum(lst::SList; init=INIT)
    init === INIT ? _minimum(next(lst), getitem(lst)) : _minimum(lst, init)
end
@inline _minimum(lst::SList, item) = _minimum(next(lst), min(getitem(lst), item))
_minimum(::Nil, item) = item
_minimum(f, ::Nil, item) = item

@inline function Base.extrema(lst::SList; init=INIT)
    if init === INIT
        item = getitem(lst)
        _extrema(next(lst), item, item)
    else
        _extrema(lst, init, init)
    end
end
function _extrema(lst::SList, mi, ma)
    item = getitem(lst)
    _extrema(next(lst), min(mi, item), max(ma, item))
end
_extrema(::Nil, mi, ma) = (mi, ma)
_extrema(f, ::Nil, mi, ma) = (mi, ma)

@specialize

@inline function unsafe_insert(lst::ForwardList, i::Number, item)
    if isone(i)
        associate(lst, item)
    else
        associate(unsafe_insert(next(lst), i - one(i), item), getitem(lst))
    end
end
function unsafe_insert(lst::ForwardItem, i::Number, item)
    isone(i) ? associate(lst, item) : ForwardList(getitem(lst), ForwardList(item, nil))
end
@inline function unsafe_insert(lst::ForwardList, i::Int, item)
    if i === -1
        associate(lst, item)
    else
        associate(unsafe_insert(next(lst), i - 1, item), getitem(lst))
    end
end
function unsafe_insert(lst::ReverseItem, i::Int, item)
    i === -1 ? ReverseList(ReverseList(nil, item), getitem(lst)) : associate(lst, item)
end

@inline Base.all(f, lst::SList) = f(getitem(lst)) ? all(f, next(lst)) : false

Base.any(f, lst::Item) = f(getitem(lst))
@inline Base.any(f, lst::SList) = f(getitem(lst)) ? true : any(f, next(lst))

@inline Base.allequal(lst::SList) = all(isequal(getitem(lst)), next(lst))

@inline function Base.allunique(lst::SList)
    n = next(lst)
    any(isequal(getitem(lst)), n) ? false : allunique(n)
end

@inline function Base.count(f, lst::SList; init=nothing)
    cnt = (f(getitem(lst)) ? 1 + count(f, next(lst)) : count(f, next(lst)))
    init === nothing ? cnt : cnt + init
end

Base.map(f, ::Nil) = nil
Base.map(f, lst::Item) = setindex(lst, f(getitem(lst)))
@inline Base.map(f, lst::SList) = associate(map(f, next(lst)), f(getitem(lst)))

@inline function Base.maximum(f, lst::SList; init=INIT)
    _maximum(f, next(lst), init === INIT ? f(getitem(lst)) : max(init, f(getitem(lst))))
end
_maximum(f, lst::SList, item) = _maximum(f, next(lst), max(item, f(getitem(lst))))

@inline function Base.minimum(f, lst::SList; init=INIT)
    _minimum(f, next(lst), init === INIT ? f(getitem(lst)) : min(init, f(getitem(lst))))
end
@inline _minimum(f, lst::SList, item) = _minimum(f, next(lst), min(f(getitem(lst)), item))

@inline function Base.extrema(f, lst::SList; init=INIT)
    if init === INIT
        item = getitem(lst)
        _extrema(f, next(lst), item, item)
    else
        _extrema(f, lst, init, init)
    end
end
@inline function _extrema(f, lst::SList, mi, ma)
    item = f(getitem(lst))
    _extrema(f, next(lst), min(mi, item), max(ma, item))
end

## mapfoldl
Base.mapfoldl(f, op, lst::ReverseList; init=INIT) = _mapfoldl(f, op, lst, init)
@inline function _mapfoldl(f, op, lst::ReverseList, init)
    op(item, _mapfoldl(f, op, next(lst), f(getitem(lst))))
end
_mapfoldl(f, op, lst::Item, ::Base._InitialValue) = f(getitem(lst))
_mapfoldl(f, op, lst::Item, item) = op(item, f(getitem(lst)))
@inline function Base.mapfoldl(f, op, lst::ForwardList; init=INIT)
    if init === INIT
        _mapfoldl(f, op, next(lst), f(getitem(lst)))
    else
        _mapfoldl(f, op, next(lst), init)
    end
end
@inline function _mapfoldl(f, op, lst::ForwardList, item)
    _mapfoldl(f, op, next(lst), op(item, f(getitem(lst))))
end

## mapfoldr
Base.mapfoldr(f, op, lst::ForwardList; init=INIT) = _mapfoldr(f, op, lst, init)
@inline function Base.mapfoldr(f, op, lst::ReverseList; init=INIT)
    if init === INIT
        _mapfoldr(f, op, next(lst), f(getitem(lst)))
    else
        _mapfoldr(f, op, lst, init)
    end
end
@inline function _mapfoldr(f, op, lst::ForwardList, init)
    op(f(getitem(lst)), _mapfoldr(f, op, next(lst), init))
end
@inline function _mapfoldr(f, op, lst::ReverseList, item)
    _mapfoldr(f, op, next(lst), op(f(getitem(lst)), item))
end
_mapfoldr(f, op, lst::Item, item) = op(f(getitem(lst)), item)
_mapfoldr(f, op, lst::Item, ::Base._InitialValue) = f(getitem(lst))

## findmax
function Base.findmax(lst::ReverseList)
    len, idx, m = _findmax(1, 1, getitem(lst), next(lst))
    (len - idx + 1, m)
end
function Base.findmax(f, lst::ReverseList)
    len, idx, m = _findmax(1, 1, f(getitem(lst)), f, next(lst))
    (len - idx + 1, m)
end
function Base.findmax(lst::ForwardList)
    _, idx, m = _findmax(1, 1, getitem(lst), next(lst))
    (idx, m)
end
function Base.findmax(f, lst::ForwardList)
    _, idx, m = _findmax(1, 1, f(getitem(lst)), f, next(lst))
    (idx, m)
end
_findmax(idx::Int, midx::Int, m, f, ::Nil) = (idx, midx, m)
_findmax(idx::Int, midx::Int, m, ::Nil) = (idx, midx, m)
@inline function _findmax(idx::Int, midx::Int, m, f, lst::SList)
    item = f(getitem(lst))
    if m >= item
        _findmax(idx + 1, midx, m, f, next(lst))
    else
        _findmax(idx + 1, idx, item, f, next(lst))
    end
end
@inline function _findmax(idx::Int, midx::Int, m, lst::SList)
    item = getitem(lst)
    if m >= item
        _findmax(idx + 1, midx, m, next(lst))
    else
        _findmax(idx + 1, idx, item, next(lst))
    end
end

## findmin
function Base.findmin(lst::ReverseList)
    len, idx, m = _findmin(1, 1, getitem(lst), next(lst))
    (len - idx + 1, m)
end
function Base.findmin(f, lst::ReverseList)
    len, idx, m = _findmax(1, 1, f(getitem(lst)), f, next(lst))
    (len - idx + 1, m)
end
function Base.findmin(lst::ForwardList)
    _, idx, m = _findmin(1, 1, getitem(lst), next(lst))
    (idx, m)
end
function Base.findmin(f, lst::ForwardList)
    _, idx, m = _findmin(1, 1, f(getitem(lst)), f, next(lst))
    (idx, m)
end
_findmin(idx::Int, midx::Int, m, ::Nil) = (idx, midx, m)
_findmin(idx::Int, midx::Int, m, f, ::Nil) = (idx, midx, m)
@inline function _findmin(idx::Int, midx::Int, m, f, lst::SList)
    item = f(getitem(lst))
    if m <= item
        _findmin(idx + 1, midx, m, f, next(lst))
    else
        _findmin(idx + 1, idx, item, f, next(lst))
    end
end
@inline function _findmin(idx::Int, midx::Int, m, lst::SList)
    item = getitem(lst)
    if m <= item
        _findmin(idx + 1, midx, m, next(lst))
    else
        _findmin(idx + 1, idx, item, next(lst))
    end
end

Base.argmax(lst::SList) = getfield(findmax(lst), 1)
Base.argmax(f, lst::SList) = getfield(findmax(f, lst), 1)

Base.argmin(lst::SList) = getfield(findmin(lst), 1)
Base.argmin(f, lst::SList) = getfield(findmin(f, lst), 1)

end

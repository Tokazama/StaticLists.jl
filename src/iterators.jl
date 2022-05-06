
Base.IteratorSize(T::Type{<:ListType}) = Base.HasLength()

Base.Iterators.reverse(x::Union{EmptyList,OneItem}) = x
Base.Iterators.reverse(x::StaticList) = Base.Iterators.Reverse(x)
Base.reverse(x::StaticList) = Base.Iterators.reverse(x)

@noinline Base.tail(::EmptyList) = throw(ArgumentError("Cannot call Base.tail on an empty list"))
Base.tail(::OneItem) = none
@inline Base.tail(x::StaticList) = @inbounds getfield(x, :tail)

Base.front(::EmptyList) = throw(ArgumentError("Cannot call Base.front on an empty list"))
@inline Base.front(::OneItem) = none
@inline Base.front(x::StaticList) = first(x, slength(x) - static(1))

@noinline Base.first(::EmptyList) = throw(ArgumentError("Cannot call first on an empty list"))
@inline Base.first(x::StaticList) = getfield(x, :first)
@inline Base.first(x::RevList) = last(parent(x))
Base.first(x::StaticList, i::Integer) = (@boundscheck checkbounds(x, i); NFirst(x, i))
Base.first(x::NFirst, i::Integer) = (@boundscheck checkbounds(x, i); NFirst(parent(x), i))
@propagate_inbounds Base.first(x::RevList, i::Integer) = reverse(last(parent(x), i))
Base.Iterators.take(x::ListType, i::Integer) = @inbounds first(x, min(i, slength(x)))

Base.last(::EmptyList) = throw(ArgumentError("Cannot call last on an empty list"))
Base.last(x::OneItem) = first(x)
@inline Base.last(x::TwoItems) = first(tail(x))
@inline Base.last(x::StaticList) = @inbounds x[slength(x)]
@inline Base.last(x::RevList) = first(parent(x))
@propagate_inbounds Base.last(x::RevList, i::Integer) = reverse(first(parent(x), i))
function Base.last(x::NFirst, i::Integer)
    @boundscheck checkbounds(x, i)
    return NFirst(@inbounds(last(parent(x), i)), slength(x))
end
function Base.last(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    _shrinkbeg(x, (slength(x) + ONE) - i)
end
Base.Iterators.drop(x::ListType, i::Integer) = @inbounds last(x, min(i, slength(x)))

Base.iterate(::EmptyList) = nothing
Base.iterate(x::StaticList) = first(x), tail(x)
Base.iterate(::OneItem, state) = nothing
@inline Base.iterate(::StaticList, s) = s === none ? nothing : (first(s), tail(s))
@inline function Base.iterate(x::NFirst, s=(parent(x), length(x)))
    len = getfield(s, 2)
    if len === 0
        return nothing
    else
        lst = getfield(s, 1)
        return first(lst), (tail(lst), len - 1)
    end
end
Base.iterate(x::RevList) = @inbounds(parent(x)[slength(x)]), 2
@inline Base.iterate(x::RevTwo, s::Int) = s === 2 ? last(parent(x)) : nothing
@inline function Base.iterate(x::RevThree, s::Int)
    @inbounds s === 2 ? (parent(x)[TWO], 3) : (s === 3 ? (first(parent(x)), 4) : nothing)
end
@inline function Base.iterate(x::RevFour, s::Int)
    if s < 4
        s === 2 ? (@inbounds(parent(x)[THREE]), 3) : (@inbounds(parent(x)[TWO]), 4)
    else
        s === 4 ? (first(parent(x)), 5) : nothing
    end
end
Base.iterate(x::RevList, s::Int) = length(x) < s ? nothing : (@inbounds(x[s]), s + 1)

@inline Base.iterate(x::StackedList) = iterate_child(children(x), 1)
@inline function iterate_child(children, child)
    itr = iterate(@inbounds(children[child]))
    itr === nothing ? nothing : (@inbounds(itr[1]), (@inbounds(itr[2]), child))
end
@inline function iterate_child(children, state, child)
    itr = iterate(@inbounds(children[child]), state)
    itr === nothing ? nothing : (@inbounds(itr[1]), (@inbounds(itr[2]), child))
end
@inline function Base.iterate(x::StackedList, state)
    c = @inbounds(state[2])
    cs = children(x)
    itr = iterate_child(cs, @inbounds(state[1]), c)
    if itr === nothing
        return c === length(cs) ? nothing : iterate_child(cs, c + 1)
    else
        return itr
    end
end

Base.only(x::OneItem) = first(x)
Base.only(x::RevList) = only(parent(x))
Base.only(x::NFirst) = length(x) === 1 ? first(x) : _list_only_error()
Base.only(::ListType) = _list_only_error()
@noinline Base.only(::None) = throw(ArgumentError("list is empty, must contain exactly 1 element"))
@noinline _list_only_error() = throw(ArgumentError("list has multiple elements, must contain exactly 1 element"))


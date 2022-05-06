
struct StackedIndex{C,I}
    child::C
    index::I
end

const UnkownChildIndex{I} = StackedIndex{Int,I}
const FirstChildIndex{I} = StackedIndex{StaticInt{1},I}
const SecondChildIndex{I} = StackedIndex{StaticInt{2},I}
const ThirdChildIndex{I} = StackedIndex{StaticInt{3},I}
const FourthChildIndex{I} = StackedIndex{StaticInt{4},I}

############
# to_index #
############
stacked_index(c::StaticInt, i::Int) = StackedIndex(dynamic(c), i)
stacked_index(c::StaticInt, i::StaticInt) = StackedIndex(c, i)

@inline function to_stacked_index(lens::TwoItems, i::Integer)
    f = first(lens)
    i <= f ? stacked_index(ONE, i - ZERO) : stacked_index(TWO, i - f)
end
@inline function to_stacked_index(lens::ThreeItems, i::Integer)
    f = lens[ONE]
    if i <= f
        return stacked_index(ONE, i - ZERO)
    else
        s = lens[TWO]
        i <= s ? stacked_index(TWO, i - f) : stacked_index(THREE, i - s)
    end
end
@inline function to_stacked_index(lens::FourItems, i::Integer)
    f = lens[ONE]
    if i <= f
        return stacked_index(ONE, i - ZERO)
    else
        s = lens[TWO]
        if i <= s
            return stacked_index(TWO, i - f)
        else
            t = lens[THREE]
            i <= t ? stacked_index(THREE, i - s) : stacked_index(FOUR, i - t)
        end
    end
end

@inline to_index(x::StackedIndex, i::Integer) = to_stacked_index(lengths(x), i)

@inline Base.eachindex(x::StaticList) = Base.OneTo(length(x))

###############
# checkbounds #
###############
Base.checkbounds(x::ListType, i) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
Base.checkbounds(::Type{Bool}, x::ListType, i::Integer) = 1 <= i <= slength(x)

# when constructing `StackedIndex` `index` is only known to be between the lengths of
# neighboring children, so if we point to a child without a neighbor on one side we have to
# expliitly check that here. For example, the first child has a neighbor on all multi-lists
# so we know that it's not greater than the length of the list but it could be below `1`.
# If we point to a middle child (e.g., child 2 when we have 3 children), then we already
# checked the bottom and top bounds.
Base.checkbounds(::Type{Bool}, x::Union{TwoLists,ThreeLists,FourLists}, i::FirstChildIndex) = 1 <= i.index
Base.checkbounds(::Type{Bool}, x::TwoLists, i::SecondChildIndex) = i.index <= slength(x)
Base.checkbounds(::Type{Bool}, x::Union{ThreeLists,FourLists}, i::SecondChildIndex) = true
Base.checkbounds(::Type{Bool}, x::ThreeLists, i::ThirdChildIndex) = i.index <= slength(x)
Base.checkbounds(::Type{Bool}, x::FourLists, i::ThirdChildIndex) = i
Base.checkbounds(::Type{Bool}, x::FourLists, i::FourthChildIndex) = i.index <= slength(x)
function Base.checkbounds(::Type{Bool}, x::TwoLists, i::UnkownChildIndex)
    i.child === 1 ? 1 <= i.index : i.index <= slength(x)
end
function Base.checkbounds(::Type{Bool}, x::ThreeLists, i::UnkownChildIndex)
    i.child === 1 ? 1 <= i.index : (i.child === 2 ? true : i.index <= slength(x))
end
function Base.checkbounds(::Type{Bool}, x::FourLists, i::UnkownChildIndex)
    i.child === 1 ? 1 <= i.index : (i.child === 2 ? true : (i.child === 3 ? true : i.index <= slength(x)))
end
Base.checkbounds(::Type{Bool}, x::ListType, i::AbstractUnitRange) = 1 <= first(i) && last(i) <= slength(x)

############
# getindex #
############
Base.getindex(x::ListType, ::Colon) = collect(x)
function Base.getindex(x::RevList, i::Integer)
    @boundscheck checkbounds(x, i)
    return @inbounds(parent(x)[(slength(x) + ONE) - i])
end

@noinline Base.getindex(x::StaticList, ::StaticInt{0}) = throw(BoundsError(none, i))
@noinline Base.getindex(::None, i::Int) = throw(BoundsError(none, i))
@noinline Base.getindex(x::None, ::StaticInt{1}) = throw(BoundsError(x, 1))
@inline Base.getindex(x::StaticList, ::StaticInt{1}) = first(x)
@noinline Base.getindex(x::Union{None,OneItem}, ::StaticInt{2}) = throw(BoundsError(x, 2))
@inline Base.getindex(x::StaticList, ::StaticInt{2}) = first(tail(x))
@noinline Base.getindex(x::Union{None,OneItem,TwoItems}, ::StaticInt{3}) = throw(BoundsError(x, 3))
@inline Base.getindex(x::StaticList, ::StaticInt{3}) = first(tail(tail(x)))
@noinline Base.getindex(x::Union{None,OneItem,TwoItems,ThreeItems}, ::StaticInt{4}) = throw(BoundsError(x, 4))
@inline Base.getindex(x::StaticList, ::StaticInt{4}) = first(tail(tail(tail(x))))
Base.getindex(x::OneItem, i::Int) = (@boundscheck checkbounds(x, i); first(x))
@inline function Base.getindex(x::TwoItems, i::Int)
    @boundscheck checkbounds(x, i)
    i === 1 ? first(x) : first(tail(x))
end
@inline function Base.getindex(x::ThreeItems, i::Int)
    @boundscheck checkbounds(x, i)
    i < 3 ? (i === 1 ? first(x) : first(tail(x))) : first(tail(tail(x)))
end
@inline function Base.getindex(x::FourItems, i::Int)
    @boundscheck checkbounds(x, i)
    if i < 3
        return (i === 1 ? first(x) : first(tail(x)))
    else
        return i === 3 ? first(tail(tail(x))) : first(tail(tail(tail(x))))
    end
end
function Base.getindex(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    first(_shrinkbeg(x, i))
end
@inline _shrinkbeg(x::StaticList, N::Int) = N === 1 ? x : _shrinkbeg(tail(x), N - 1)
@generated function _shrinkbeg(x::StaticList, ::StaticInt{N}) where {N}
    out = :x
    for _ in 1:(N - 1)
        out = :(tail($(out)))
    end
    Expr(:block, Expr(:meta, :inline), out)
end
Base.get(x::StaticList, i::Integer, d) = checkbounds(Bool, x, i) ? @inbounds(x[i]) : d

Base.setindex(x::OneItem, v, i::Int) = (@boundscheck checkbounds(x, i); list(v))
function Base.setindex(x::TwoItems, v, i::Int)
    @boundscheck checkbounds(x, i)
    i === 1 ? unsafe_setindex(x, v, ONE) : unsafe_setindex(x, v, TWO)
end
function Base.setindex(x::ThreeItems, v, i::Int)
    @boundscheck checkbounds(x, i)
    if i === 1
        return unsafe_setindex(x, v, ONE)
    elseif i === 2
        return unsafe_setindex(x, v, TWO)
    else
        return unsafe_setindex(x, v, THREE)
    end
end
function Base.setindex(x::FourLists, v, i::Int)
    @boundscheck checkbounds(x, i)
    if i < 3
        return i === 1 ? unsafe_setindex(x, v, ONE) : unsafe_setindex(x, v, TWO)
    else
        return i === 3 ? unsafe_setindex(x, v, THREE) : unsafe_setindex(x, v, FOUR)
    end
end
@inline function Base.setindex(x::StaticList, v, i::Int)
    @boundscheck checkbounds(x, i)
    i === 1 ? cons(v, tail(x)) : cons(first(x), @inbounds(setindex(tail(x), v, i - 1)))
end
function Base.setindex(x::StaticList, v, i::StaticInt)
    @boundscheck checkbounds(x, i)
    unsafe_setindex(x, v, i)
end
@generated function unsafe_setindex(x0::StaticList, v, ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(cons(v, Base.tail($(Symbol(:x, N-1)))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

##########
# NFirst #
##########
function Base.getindex(x::NFirst, i::Integer)
    @boundscheck checkbounds(x, i)
    return @inbounds(parent(x)[i])
end

###############
# StackedList #
###############
@propagate_inbounds Base.getindex(x::StackedList, i::Integer) = x[to_index(x, i)]
function Base.getindex(x::StackedList, i::StackedIndex)
    @boundscheck checkbounds(x, i)
    @inbounds children[i.child][i.index]
end


module StaticLists

using Base: front, tail, @propagate_inbounds, setindex
using Static

export cons, deleteat, insert, list

const ZERO = static(0)
const ONE = static(1)
const TWO = static(2)
const THREE = static(3)
const FOUR = static(4)

struct Nil end

const nil = Nil()

@nospecialize

"""
    StaticList(first, tail)

A statically-sized, singly-linked StaticList.
"""
struct StaticList{F,T,L}
    first::F
    tail::T
    length::L
end

const None = StaticList{Nil,Nil,StaticInt{0}}
const none = StaticList(nil, nil, ZERO)

const OneItem{T} = StaticList{T,Nil,StaticInt{1}}
const TwoItems{T1,T2} = StaticList{T1,OneItem{T2},StaticInt{2}}
const ThreeItems{T1,T2,T3} = StaticList{T1,TwoItems{T2,T3},StaticInt{3}}
const FourItems{T1,T2,T3,T4} = StaticList{T1,ThreeItems{T2,T3,T4},StaticInt{4}}

const RevList{F,T,L} = Iterators.Reverse{StaticList{F,T,L}}
const RevTwo{T1,T2} = RevList{T2,OneItem{T1},StaticInt{2}}
const RevThree{T1,T2,T3} = RevList{T3,TwoItems{T2,T1},StaticInt{3}}
const RevFour{T1,T2,T3,T4} = RevList{T4,ThreeItems{T3,T2,T1},StaticInt{4}}

const EmptyList = Union{None,RevList{None}}

struct NFirst{P,L}
    parent::P
    length::L
end

struct StackedList{C,L}
    children::C
    lengths::L  # accumulating length of each child
end
StackedList(x::Union{TwoItems,ThreeItems,FourItems}) = StackedList(x, sumlengths(x))
@inline sumlengths(x::StaticList) = _sumlengths(slength(first(x)), tail(x))
@inline _sumlengths(prev, x) = cons(prev, _sumlengths(prev + slength(first(x)), tail(x)))
_sumlengths(prev, ::None) = list(prev)

const TwoLists{C1,C2,L1,L2} = StackedList{TwoItems{C1,C2},TwoItems{L1,L2}}
const ThreeLists{C1,C2,C3,L1,L2,L3} = StackedList{ThreeItems{C1,C2,C3},ThreeItems{L1,L2,L3}}
const FourLists{C1,C2,C3,C4,L1,L2,L3,L4} = StackedList{FourItems{C1,C2,C3,C4},FourItems{L1,L2,L3,L4}}

children(x::StackedList) = getfield(x, 1)

@inline nchildren(x::StackedList) = slength(chidlren(x))

lengths(x::StackedList) = getfield(x, :lengths)

const ListType = Union{NFirst,StaticList,RevList,StackedList}

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

Base.parent(x::StaticList) = x
Base.parent(x::Union{NFirst,RevList}) = getfield(x, 1)

"""
    list(args...)

Composes a list where each argument is a member of the list.
"""
list() = none
# this is a trick to speed up compilation of the first item
list(x) = StaticList(x, nil, ONE)
@inline list(@nospecialize(x), @nospecialize(args...)) = cons(x, list(args...))

@inline cons(x, y) = cons(x, list(y))
@inline cons(x, ::None) = list(x)
@generated cons(x, y::OneItem) = :(StaticList(x, y, $(TWO)))
@generated cons(x, y::TwoItems) = :(StaticList(x, y, $(THREE)))
@generated cons(x, y::ThreeItems) = :(StaticList(x, y, $(FOUR)))
@inline cons(x, y::StaticList) = StaticList(x, y, slength(y) + ONE)

Base.values(x::Union{NFirst,StaticList,RevList}) = x

Base.eltype(x::ListType) = eltype(typeof(x))
Base.eltype(T::Type{<:NFirst}) = eltype(T.parameters[1])
Base.eltype(T::Type{<:StackedList}) = eltype(T.parameters[1])
Base.eltype(::Type{<:EmptyList}) = Union{}
Base.eltype(T::Type{<:OneItem}) = T.parameters[1]
@inline function Base.eltype(T::Type{<:TwoItems})
    typejoin(T.parameters[1], T.parameters[2].parameters[1])
end
@inline function Base.eltype(T::Type{<:StaticList})
    typejoin(T.parameters[1], eltype(T.parameters[2]))
end

###
# Indexing
###
Base.collect(x::RevList) = _reverse(x, slength(x))
@generated function _reverse(x0::StaticList, ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :none
    for i in 0:(N - 1)
        out = :(cons(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end
Base.collect(x::StaticList) = x
# takes the first `N` values and attaches them to the new root/tail
Base.collect(x::NFirst) = _reroot(parent(x), nil, slength(x))
@generated function _reroot(x0::StaticList, root::StaticList, ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :root
    for i in (N - 1):-1:0
        out = :(cons(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end
@inline function _reroot(x0::StaticList, root::StaticList, N::Int)
    N === 1 ? cons(first(x0), root) : cons(first(x0), _reroot(tail(x), root, N - 1))
end

include("indexing.jl")

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

Base.in(x, lst::RevList) = in(x, parent(lst))
@inline function Base.in(x, lst::Union{NFirst,StaticList})
    for i in lst
        i == x && return true
    end
    return false
end

Base.isempty(::EmptyList) = true
Base.isempty(::Union{StaticList,RevList}) = false
Base.isempty(x::NFirst) = iszero(slength(x))

Base.empty(::ListType) = none

slength(x::RevList) = slength(parent(x))
slength(x::Union{StaticList,NFirst}) = getfield(x, :length)
@inline slength(x::StackedList) = last(lengths(x))
Base.length(::None) = 0
Base.length(::OneItem) = 1
Base.length(::TwoItems) = 2
Base.length(::ThreeItems) = 3
Base.length(::FourItems) = 4
@inline Base.length(x::StaticList) = Int(slength(x))
@inline Base.length(x::Union{NFirst,RevList,StackedList}) = Int(slength(x))
Base.size(x::ListType) = (length(x),)

include("iterators.jl")

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

Base.map(f, ::None) = none
@inline Base.map(f, x::StaticList) = _genmap(f, x, slength(x))
@generated function _genmap(f, x0::StaticList, ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :none
    for i in (N - 1):-1:0
        out = :(cons(f(first($(Symbol(:x, i)))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

@inline Base.mapfoldl(f, op, x::StaticList; init=nil) = _mapfoldl(f, op, x, init, slength(x))
@generated function _mapfoldl(f, op, x0::StaticList, init::I, ::StaticInt{N}) where {I,N}
    out = ntails_expr(N)
    if I <: Nil
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

@inline Base.mapfoldr(f, op, x::StaticList; init=nil) = _mapfoldr(f, op, x, init, slength(x))
@generated function _mapfoldr(f, op, x0::StaticList, init::I, ::StaticInt{N}) where {I,N}
    out = ntails_expr(N)
    if I <: Nil
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

@inline function Base.accumulate(op, lst::StaticList; init=nil)
    init === nil ? _accum(op, first(lst), tail(lst)) : _accum(op, init, lst)
end
_accum(op, prev, ::None) = list(prev)
@inline _accum(op, prev, lst::StaticList) = cons(prev, _accum(op, op(prev, first(lst)), tail(lst)))

"""
    insert(list, index, item) -> out

Returns a list where `item` is inserted at `index`. `index` is the index of item in `out`.
"""
@inline function insert(x::StaticList, i::Integer, v)
    @boundscheck 1 <= i <= (length(x) + 1)
    unsafe_insert(x, i, v)
end
@inline unsafe_insert(::EmptyList, ::Int, v) = list(v)
@inline unsafe_insert(x::OneItem, i::Int, v) = i === 1 ? cons(v, x) : list(first(x), v)
@inline function unsafe_insert(x::StaticList, i::Int, v)
    i === 1 ? cons(v, x) : cons(first(x), unsafe_insert(tail(x), i - 1, v))
end
@generated function unsafe_insert(x0::StaticList, ::StaticInt{N}, v) where {N}
    out = ntails_expr(N - 1)
    r = :(cons(v, $(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

"""
    deleteat(list, index)

Returns a list without the value corresponding to `index`.
"""
function deleteat(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_deleteat(x, i)
end
unsafe_deleteat(x::OneItem, i::Int) = none
@inline unsafe_deleteat(x::TwoItems, i::Int) = i === 1 ? tail(x) : list(first(x))
@inline function unsafe_deleteat(x::StaticList, i::Int)
    i === 1 ? tail(x) : cons(first(x), unsafe_deleteat(tail(x), i - 1))
end
@generated function unsafe_deleteat(x0::StaticList, ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(Base.tail($(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

"""
    popat(list, index) -> (list[index], deleteat(list, index))

Returns the value at `key` and the StaticList without the value.
"""
function popat(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_popat(x, i)
end
@inline unsafe_popat(x::OneItem, i::Int) = first(x), none
@inline function unsafe_popat(x::TwoItems, i::Int)
    i === 1 ? (first(x), tail(x)) : (last(x), list(first(x)))
end
@inline function unsafe_popat(x::StaticList, i::Int)
    if i === 1
        return first(x), tail(x)
    else
        f, t = unsafe_popat(tail(x), i - 1)
        return f, cons(first(x), t)
    end
end
@generated function unsafe_popat(x0::StaticList, ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(Base.tail($(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, :(first($(Symbol(:x, N - 1))), $r))
    return out
end

## findfirst
@inline function Base.findfirst(f::Function, lst::StaticList)
    index = _findfirst(f, lst, slength(lst))
    if index === 0
        return nothing
    else
        return index
    end
end
@generated function _findfirst(f, x1::StaticList, ::StaticInt{N}) where {N}
    out = :0
    for i in N:-1:2
        out = Expr(:block, :($(Symbol(:x, i)) = tail($(Symbol(:x, i - 1)))), Expr(:if, :(f(first($(Symbol(:x, i))))), i, out))
    end
    Expr(:block, Expr(:meta, :inline), Expr(:if, :(f(first(x1))), 1, out))
end

Base.show(io::IO, x::Union{ListType,Nil}) = show(io, MIME"text/plain"(), x)
Base.show(io::IO, ::MIME"text/plain", ::Nil) = print(io, "nil")
@noinline function Base.show(io::IO, M::MIME"text/plain", x::ListType)
    str = "list("
    N = length(x)
    i = 1
    for x_i in x
        str *= repr(x_i)
        if N !== i
            str *= ", "
        end
        i += 1
    end
    print(io, str * ")")
end


@specialize

end

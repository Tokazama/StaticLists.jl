module StaticLists

using Base: front, tail, @propagate_inbounds
using Static

export cons, deleteat, insert, list

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
struct StaticList{F,T}
    first::F
    tail::T
end

const None = StaticList{Nil,Nil}
const none = StaticList(nil, nil)

const OneItem{T} = StaticList{T,Nil}
const TwoItems{T1,T2} = StaticList{T1,OneItem{T2}}
const ThreeItems{T1,T2,T3} = StaticList{T1,TwoItems{T2,T3}}
const FourItems{T1,T2,T3,T4} = StaticList{T1,ThreeItems{T2,T3,T4}}

const RevList{F,T,L} = Iterators.Reverse{StaticList{F,T}}
const RevTwo{T1,T2} = RevList{T2,OneItem{T1}}
const RevThree{T1,T2,T3} = RevList{T3,TwoItems{T2,T1}}
const RevFour{T1,T2,T3,T4} = RevList{T4,ThreeItems{T3,T2,T1}}

const EmptyList = Union{None,RevList{None}}

struct NFirst{P,L}
    parent::P
    length::L
end

const ListType = Union{NFirst,StaticList,RevList}

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
list(x) = StaticList(x, nil)
@inline list(@nospecialize(x), @nospecialize(args...)) = cons(x, list(args...))

@inline cons(x, y) = cons(x, list(y))
@inline cons(x, ::None) = list(x)
@generated cons(x, y::OneItem) = :(StaticList(x, y))
@generated cons(x, y::TwoItems) = :(StaticList(x, y))
@generated cons(x, y::ThreeItems) = :(StaticList(x, y))
@inline cons(x, y::StaticList) = StaticList(x, y)
@inline cons(x::StaticList, y) = unsafe_insert(x, slength(x) + ONE, y)
#@inline cons(x::StaticList, y::StaticList) = cat(x, y)

Base.values(x::Union{NFirst,StaticList,RevList}) = x

Base.eltype(x::ListType) = eltype(typeof(x))
Base.eltype(T::Type{<:NFirst}) = eltype(T.parameters[1])
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
Base.checkbounds(x::ListType, i) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
Base.checkbounds(::Type{Bool}, x::ListType, i::Integer) = 1 <= i <= slength(x)
function Base.checkbounds(::Type{Bool}, x::StaticList, i::AbstractUnitRange)
    checkbounds(Bool, x, first(x)) && checkbounds(Bool, x, last(x))
end

@inline Base.eachindex(x::StaticList) = Base.OneTo(length(x))

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

Base.getindex(x::ListType, ::Colon) = collect(x)
function Base.getindex(x::RevList, i::Integer)
    @boundscheck checkbounds(x, i)
    return _getindex(parent(x), (slength(x) + ONE) - i)
end
function Base.getindex(x::Union{StaticList,NFirst}, i::Integer)
    @boundscheck checkbounds(x, i)
    return _getindex(parent(x), i)
end
@inline _getindex(x::OneItem, ::Int) = first(x)
@inline _getindex(x::TwoItems, i::Int) = i === 1 ? first(x) : last(x)
@inline function _getindex(x::ThreeItems, i::Int)
    i === 1 ? first(x) : (i === 2 ? @inbounds(x[TWO]) : @inbounds(x[THREE]))
end
@inline _getindex(x::StaticList, i::Int) = i === 1 ? first(x) : _getindex(tail(x), i - 1)
@inline _getindex(x::StaticList, i::StaticInt) = first(_shrinkbeg(x, i))
@inline _shrinkbeg(x::StaticList, N::Int) = N === 1 ? x : _shrinkbeg(tail(x), N - 1)
@generated function _shrinkbeg(x::StaticList, ::StaticInt{N}) where {N}
    out = :x
    for _ in 1:(N - 1)
        out = :(tail($(out)))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

@inline Base.get(x::StaticList, i::Integer, d) = checkbounds(Bool, x, i) ? _getindex(x, i) : d

function Base.setindex(x::StaticList, v, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_setindex(x, v, i)
end
@inline unsafe_setindex(x::OneItem, v, i::Int) = list(v)
@inline unsafe_setindex(x::TwoItems, v, i::Int) = i === 1 ? cons(v, tail(x)) : cons(first(x), v)
@inline function unsafe_setindex(x::StaticList, v, i::Int)
    i === 1 ? cons(v, tail(x)) : cons(first(x), unsafe_setindex(tail(x), v, i - 1))
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
slength(x::NFirst) = getfield(x, :length)
slength(x::StaticList) = StaticInt(length(x))
Base.length(::None) = 0
Base.length(::OneItem) = 1
Base.length(::TwoItems) = 2
Base.length(::ThreeItems) = 3
Base.length(::FourItems) = 4
@inline Base.length(x::StaticList) = length(tail(x)) + 1
@inline Base.length(x::RevList) = length(parent(x))
@inline Base.length(x::NFirst) = Int(slength(x))
Base.size(x::ListType) = (length(x),)

###
# Iterators
###
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
Base.iterate(x::RevList) = _getindex(parent(x), slength(x)), 2
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

Base.only(x::OneItem) = first(x)
Base.only(x::RevList) = only(parent(x))
Base.only(x::NFirst) = length(x) === 1 ? first(x) : _list_only_error()
Base.only(::ListType) = _list_only_error()
@noinline Base.only(::None) = throw(ArgumentError("list is empty, must contain exactly 1 element"))
@noinline _list_only_error() = throw(ArgumentError("list has multiple elements, must contain exactly 1 element"))

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

###
# show
###
Base.show(io::IO, x::Union{StaticList,Nil,NFirst}) = show(io, MIME"text/plain"(), x)
Base.show(io::IO, ::MIME"text/plain", ::Nil) = print(io, "nil")
@noinline Base.show(io::IO, ::MIME"text/plain", x::NFirst) = print(io, "NFirst(" * strlist(x) * ")")
@noinline Base.show(io::IO, ::MIME"text/plain", x::StaticList) = print(io, "list(" * strlist(x) * ")")
@noinline function strlist(x)
    str = ""
    N = length(x)
    i = 1
    for x_i in x
        str *= repr(x_i)
        if N !== i
            str *= ", "
        end
        i += 1
    end
    return str
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

@specialize

end

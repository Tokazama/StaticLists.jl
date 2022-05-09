module StaticLists

using Base: @propagate_inbounds, tail, setindex
using Static

export deleteat, insert, list, popat

const ONE = StaticInt(1)

@nospecialize

const INIT = Base._InitialValue()

struct Nil end

const nil = Nil()

@noinline Base.first(::Nil) = throw(ArgumentError("Cannot call first on an empty list"))
@noinline Base.last(::Nil) = throw(ArgumentError("Cannot call last on an empty list"))
@noinline Base.tail(::Nil) = throw(ArgumentError("Cannot call Base.tail on an empty list"))

function ntails_expr(s::Union{Symbol,Expr}, N::Int)
    out = s
    for _ in 1:N
        out = :(getfield($(out), 2))
    end
    ifelse(N === 0, out, :(@inbounds($(out))))
end
_getexpr(s::Union{Symbol,Expr}, N::Int) = Expr(:call, :getfield, ntails_expr(s, N - 1), 1)

struct StaticList{F,T,L}
    first::F
    tail::T
    length::L
end

const OneItem{T} = StaticList{T,Nil,StaticInt{1}}
const TwoItems{T1,T2} = StaticList{T1,OneItem{T2},StaticInt{2}}
const ReverseList{F,T,L} = Iterators.Reverse{StaticList{F,T,L}}
const ReverseOne{T} = ReverseList{T,Nil,StaticInt{1}}

@inline Base.first(x::StaticList) = getfield(x, :first)

@inline Base.tail(x::StaticList) = @inbounds getfield(x, :tail)

@inline Base.last(x::StaticList) = @inbounds(x[slength(x)])

Base.reverse(x::StaticList) = _reverse(x, slength(x))
Base.collect(x::StaticList) = x
Base.collect(x::ReverseList) = _reverse(getfield(x, 1), slength(x))
@generated function _reverse(x::StaticList, ::StaticInt{N}) where {N}
    out = Expr(:tuple)
    for i in N:-1:1
        push!(out.args, :(_getindex(x, $(StaticInt(i)))))
    end
    Expr(:block, Expr(:meta, :inline), :(_list($(out), $(static(N)))))
end

@inline Base.eachindex(x::StaticList) = Base.OneTo(length(x))

Base.IteratorSize(T::Type{<:StaticList}) = Base.HasLength()

Base.only(x::OneItem) = first(x)
@noinline Base.only(x::StaticList) = throw(ArgumentError("list has multiple elements, must contain exactly 1 element"))
@noinline Base.only(::Nil) = throw(ArgumentError("list is empty, must contain exactly 1 element"))

Base.checkbounds(x::Union{StaticList,ReverseList}, i) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
Base.checkbounds(::Type{Bool}, x::Union{StaticList,ReverseList}, i::Integer) = 1 <= i <= slength(x)
Base.checkbounds(::Type{Bool}, x::StaticList, i::AbstractUnitRange) = 1 <= first(i) && last(i) <= slength(x)


function Base.get(x::Union{StaticList,ReverseList}, i::Integer, d)
    checkbounds(Bool, x, i) ? @inbounds(x[i]) : d
end
Base.getindex(x::StaticList, ::Colon) = x
function Base.getindex(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    _getindex(x, i)
end
@inline _getindex(x::StaticList, i::Int) = i === 1 ? first(x) : _getindex(tail(x), i - 1)
@generated function _getindex(x::StaticList, ::StaticInt{N}) where {N}
    Expr(:block, Expr(:meta, :inline), _getexpr(:x, N))
end
function Base.getindex(x::ReverseList, i::Integer)
    @boundscheck checkbounds(x, i)
    _getindex(getfield(x, 1), (slength(x) + ONE) - i)
end

function Base.setindex(x::StaticList, v, i::Integer)
    @boundscheck checkbounds(x, i)
    return _setindex(x, v, i)
end
@inline function _setindex(x::StaticList, v, i::Int)
    if i === 1
        return StaticList(v, tail(x), slength(x))
    else
        return StaticList(first(x), _setindex(tail(x), v, i - 1), slength(x))
    end
end
_setindex(x::StaticList, v, i::StaticInt) = __setindex(x, v, i, slength(x))
@generated function __setindex(x::StaticList, v, ::StaticInt{N}, ::StaticInt{L}) where {N,L}
    out = :(StaticList(v, $(ntails_expr(:x, N)), $(StaticInt(L - N + 1))))
    for i in (N-1):-1:1
        out = :(StaticList($(_getexpr(:x, i)), $(out), $(StaticInt(L - i + 1))))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

"""
    list(args...)

Composes a list where each argument is a member of the list.
"""
list(args...) = _list(args, StaticInt(nfields(args)))
@generated function _list(args::Tuple, ::StaticInt{N}) where {N}
    out = :nil
    itr = 0
    for i in N:-1:1
        itr += 1
        out = :(StaticList(getfield(args, $(i)), $(out), $(static(itr))))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

Base.values(x::StaticList) = x

Base.eltype(x::StaticList) = eltype(typeof(x))
Base.eltype(::Type{Nil}) = Union{}
Base.eltype(T::Type{<:OneItem}) = T.parameters[1]
Base.eltype(T::Type{<:TwoItems}) = typejoin(T.parameters[1], eltype(T.parameters[2]))
@inline function Base.eltype(T::Type{<:StaticList})
    t = T.parameters[2]
    typejoin(typejoin(T.parameters[1], t.parameters[1]), eltype(t.parameters[2]))
end

###
# Comparison
###
Base.:(==)(::Nil, ::Nil) = true
function Base.:(==)(x::StaticList, y::StaticList)
    if slength(x) === slength(y)
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

Base.in(val, x::StaticList) = _findfirst(==(val), x, slength(x)) !== 0

Base.isempty(::Nil) = true
Base.isempty(::StaticList) = false

Base.empty(::StaticList) = nil

slength(::Nil) = StaticInt(0)
slength(x::StaticList) = getfield(x, :length)
slength(x::ReverseList) = slength(getfield(x, 1))
@inline Base.length(x::Union{StaticList,Nil,ReverseList}) = Int(slength(x))
Base.size(x::Union{StaticList,Nil}) = (length(x),)

Base.iterate(::Union{Nil,Iterators.Reverse{Nil}}) = nothing
Base.iterate(x::Union{StaticList,ReverseList}) = first(x), 2
Base.iterate(::Union{OneItem,ReverseOne}, ::Int) = nothing
@inline Base.iterate(x::TwoItems, s::Int) = s === 2 ? (first(tail(x)), 3) : nothing
@inline function Base.iterate(x::Union{StaticList,ReverseList}, s::Int)
    if s > length(x)
        return nothing
    else
        return @inbounds(x[s]), s + 1
    end
end

Base.map(f, ::Nil) = nil
@inline Base.map(f, x::StaticList) = _genmap(f, x, slength(x))
@generated function _genmap(f, x::StaticList, ::StaticInt{N}) where {N}
    out = :nil
    cnt = 1
    for i in N:-1:1
        out = :(StaticList(f($(_getexpr(:x, i))), $(out), $(StaticInt(cnt))))
        cnt += 1
    end
    Expr(:block,  Expr(:meta, :inline), out)
end

_is_init(::Base._InitialValue) = True()
_is_init(x) = False()

# TODO errors on Nil
@inline Base.mapfoldl(f, op, x::StaticList; init=INIT) = _mapfoldl(f, op, x, init, _is_init(init), slength(x))
@generated function _mapfoldl(f, op, x::StaticList, init, ::IsInit, ::StaticInt{N}) where {IsInit,N}
    if IsInit <: True
        out = :(f(first(x)))
        idx = 2
    else
        out = :init
        idx = 1
    end
    for i in idx:N
        out = :(op($(out), f($(_getexpr(:x, i)))))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

@inline Base.mapfoldr(f, op, x::StaticList; init=INIT) = _mapfoldr(f, op, x, init, _is_init(init), slength(x))
@generated function _mapfoldr(f, op, x::StaticList, init, ::IsInit, ::StaticInt{N}) where {IsInit,N}
    if IsInit <: True
        out = :(f($(_getexpr(:x, N))))
        idx = N - 1
    else
        out = :init
        idx = N
    end
    for i in idx:-1:1
        out = :(op(f($(_getexpr(:x, i))), $(out)))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

@inline function Base.accumulate(op, lst::StaticList; init=nil)
    init === nil ? _accum(op, first(lst), tail(lst)) : _accum(op, init, lst)
end
_accum(op, prev, ::Nil) = list(prev)
@inline function _accum(op, prev, x::StaticList)
    StaticList(prev, _accum(op, op(prev, first(x)), tail(x)), slength(x))
end

"""
    insert(list, index, item) -> out

Returns a list where `item` is inserted at `index`. `index` is the index of item in `out`.
"""
@inline function insert(x::StaticList, i::Integer, v)
    @boundscheck 1 <= i <= (length(x) + 1)
    unsafe_insert(x, i, v)
end
@inline unsafe_insert(::Nil, ::Int, v) = StaticList(v, nil, ONE)
@inline function unsafe_insert(x::StaticList, i::Int, v)
    if i === 1
        return StaticList(v, x, slength(x) + ONE)
    else
        return StaticList(first(x), unsafe_insert(tail(x), i - 1, v), slength(x) + ONE)
    end
end
unsafe_insert(x::StaticList, i::StaticInt, v) = _insert(x, i, slength(x), v)
@generated function _insert(x::StaticList, ::StaticInt{N}, ::StaticInt{L}, v) where {N,L}
    out = :(StaticList(v, $(ntails_expr(:x, N - 1)), $(StaticInt(L - N + 2))))
    for i in (N-1):-1:1
        out = :(StaticList($(_getexpr(:x, i)), $(out), $(StaticInt(L - i + 2))))
    end
    Expr(:block, Expr(:meta, :inline), out)

end

"""
    deleteat(list, index)

Returns a list without the value corresponding to `index`.
"""
function deleteat(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_deleteat(x, i)
end
unsafe_deleteat(x::Union{OneItem,ReverseOne}, i::Int) = nil
@inline unsafe_deleteat(x::TwoItems, i::Int) = i === 1 ? tail(x) : list(first(x))
@inline function unsafe_deleteat(x::StaticList, i::Int)
    if i === 1
        return tail(x)
    else
        return StaticList(first(x), unsafe_deleteat(tail(x), i - 1), slength(x) - ONE)
    end
end
unsafe_deleteat(x::StaticList, i::StaticInt) = _delete(x, i, slength(x))
@generated function _delete(x::StaticList, ::StaticInt{N}, ::StaticInt{L}) where {N,L}
    out = ntails_expr(:x, N)
    for i in (N-1):-1:1
        out = :(StaticList($(_getexpr(:x, i)), $(out), $(StaticInt(L - i))))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

"""
    popat(list, index) -> (list[index], deleteat(list, index))

Returns the value at `key` and the StaticList without the value.
"""
function popat(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_popat(x, i)
end
@inline unsafe_popat(x::Union{OneItem,ReverseOne}, i::Int) = first(x), nil
@inline function unsafe_popat(x::TwoItems, i::Int)
    i === 1 ? (first(x), tail(x)) : (last(x), list(first(x)))
end
@inline function unsafe_popat(x::StaticList, i::Int)
    if i === 1
        return first(x), tail(x)
    else
        f, t = unsafe_popat(tail(x), i - 1)
        return f, StaticList(first(x), t, slength(x) - ONE)
    end
end
unsafe_popat(x::StaticList, i::StaticInt) = _popat(x, i, slength(x))
@generated function _popat(x::StaticList, ::StaticInt{N}, ::StaticInt{L}) where {N,L}
    out = ntails_expr(:x, N)
    for i in (N-1):-1:1
        out = :(StaticList($(_getexpr(:x, i)), $(out), $(StaticInt(L - i))))
    end
    out = Expr(:tuple, _getexpr(:x, N), out)
    Expr(:block, Expr(:meta, :inline), out)
end

## findfirst
@inline function Base.findfirst(f::Function, lst::StaticList)
    index = _findfirst(f, lst, slength(lst))
    index === 0 ? nothing : index
end
@generated function _findfirst(f, x1::StaticList, ::StaticInt{N}) where {N}
    out = :0
    for i in N:-1:2
        out = Expr(:block, :($(Symbol(:x, i)) = tail($(Symbol(:x, i - 1)))), Expr(:if, :(f(first($(Symbol(:x, i))))), i, out))
    end
    Expr(:block, Expr(:meta, :inline), Expr(:if, :(f(first(x1))), 1, out))
end

Base.filter(f, ::Nil) = nil
@inline function Base.filter(f, x::StaticList)
    fst = first(x)
    if f(fst)
        y = filter(f, tail(x))
        return StaticList(fst, y, slength(y) + ONE)
    else
        return filter(f, tail(x))
    end
end

@noinline Base.show(io::IO, x::Union{StaticList,Nil}) = show(io, MIME"text/plain"(), x)
@noinline function Base.show(io::IO, M::MIME"text/plain", x::Union{StaticList,Nil})
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

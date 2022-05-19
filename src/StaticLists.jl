module StaticLists

using Base: @propagate_inbounds, tail, setindex
using Static

export deleteat, insert, list, popat

const ONE = StaticInt(1)
const IntType = Union{Int,StaticInt}

@inline add1(N::Int) = N + 1
@inline add1(::StaticInt{N}) where {N} = StaticInt(N + 1)

@inline sub1(N::Int) = N - 1
@inline sub1(::StaticInt{N}) where {N} = StaticInt(N - 1)

const INIT = Base._InitialValue()

struct Nil end

const nil = Nil()

struct SkipPosition end

const skippos = SkipPosition()

@inline maybe_skip(f, x) = f(x) ? x : skippos

@nospecialize

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

Base.reverse(x::ReverseList) = getfield(x, 1)

@inline Base.tail(x::StaticList) = @inbounds getfield(x, :tail)

#########
# assoc #
#########
@inline assoc(::SkipPosition, ::Nil) = nil
@inline assoc(::SkipPosition, y::StaticList) = y
@inline assoc(x, ::Nil) = StaticList(x, nil, ONE)
@inline assoc(x, y::StaticList) = StaticList(x, y, add1(y.length))

#########
# first #
#########
@inline Base.first(x::StaticList) = getfield(x, :first)
@inline Base.first(x::ReverseList) = last(reverse(x))

########
# last #
########
@inline Base.last(x::StaticList) = @inbounds(x[slength(x)])
@inline Base.last(x::ReverseList) = first(reverse(x))

Base.Iterators.reverse(::Nil) = nil
Base.Iterators.reverse(x::StaticList) = Iterators.Reverse(x)
Base.reverse(x::StaticList) = _reverse(x, slength(x))
Base.collect(x::StaticList) = x
@inline Base.collect(x::ReverseList) = _reverse(reverse(x), slength(x))
@generated function _reverse(x::StaticList, ::StaticInt{N}) where {N}
    out = Expr(:tuple)
    for i in N:-1:1
        push!(out.args, _getexpr(:x, i))
    end
    Expr(:block, Expr(:meta, :inline), :(_list($(out), $(StaticInt(N)))))
end

@inline Base.eachindex(x::Union{StaticList,ReverseList}) = Base.OneTo(length(x))

Base.IteratorSize(T::Type{<:StaticList}) = Base.HasLength()
Base.IteratorSize(T::Type{Nil}) = Base.HasLength()

Base.only(x::OneItem) = first(x)
@noinline Base.only(x::StaticList) = throw(ArgumentError("list has multiple elements, must contain exactly 1 element"))

Base.checkbounds(x::Union{StaticList,ReverseList}, i) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
@inline Base.checkbounds(::Type{Bool}, x::Union{StaticList,ReverseList}, i) = _checkbounds(slength(x), i)
@inline _checkbounds(::StaticInt{N}, i::Int) where {N} = 1 <= i && i <= N
@inline _checkbounds(::StaticInt{N}, ::StaticInt{i}) where {N,i} = 1 <= i && i <= N

@inline function Base.get(x::Union{StaticList,ReverseList}, i::Integer, d)
    if checkbounds(Bool, x, i)
        return @inbounds(x[i])
    else
        return d
    end
end
Base.getindex(x::StaticList, ::Colon) = x
Base.getindex(x::ReverseList, ::Colon) = collect(x)
function Base.getindex(x::StaticList, i::Int)
    @boundscheck checkbounds(x, i)
    return _getindex(x, i)
end
@inline _getindex(x::StaticList, i::Int) = i === 1 ? first(x) : _getindex(tail(x), i - 1)
Base.getindex(x::StaticList, i::StaticInt) = _getindex(x, i, getfield(x, :length))
@generated function _getindex(x::StaticList, i::StaticInt{N}, ::StaticInt{L}) where {N,L}
    if 1 <= N && N <= L
        Expr(:block, Expr(:meta, :inline), _getexpr(:x, N))
    else
        :(throw(BoundsError(x, i)))
    end
end
@propagate_inbounds function Base.getindex(x::ReverseList, i::Integer)
    reverse(x)[add1(slength(x)) - i]
end
function Base.setindex(x::StaticList, v, i::Int)
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
Base.setindex(x::StaticList, v, i::StaticInt) = _setindex(x, v, i, slength(x))
@generated function _setindex(x::StaticList, v, i::StaticInt{N}, ::StaticInt{L}) where {N,L}
    if 1 <= N && N <= L
        out = :(StaticList(v, $(ntails_expr(:x, N)), $(StaticInt(L - N + 1))))
        for i in (N-1):-1:1
            out = :(StaticList($(_getexpr(:x, i)), $(out), $(StaticInt(L - i + 1))))
        end
        Expr(:block, Expr(:meta, :inline), out)
    else
        :(throw(BoundsError(x, i)))
    end
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
        out = :(StaticList(getfield(args, $(i)), $(out), $(StaticInt(itr))))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

Base.values(x::Union{StaticList,ReverseList}) = x

##########
# eltype #
##########
Base.eltype(x::Union{StaticList,ReverseList,Nil}) = eltype(typeof(x))
Base.eltype(::Type{Nil}) = Union{}
Base.eltype(T::Type{<:OneItem}) = T.parameters[1]
Base.eltype(T::Type{<:TwoItems}) = typejoin(T.parameters[1], eltype(T.parameters[2]))
@inline function Base.eltype(T::Type{<:StaticList})
    t = T.parameters[2]
    typejoin(typejoin(T.parameters[1], t.parameters[1]), eltype(t.parameters[2]))
end
Base.eltype(T::Type{<:ReverseList}) = eltype(T.parameters[1])

###
# Comparison
###
@inline function Base.:(==)(x::Union{StaticList,Nil}, y::Union{StaticList,Nil})
    slength(x) === slength(y) ? _iseq(x, y) : false
end
_iseq(::Nil, ::Nil) = true
@inline _iseq(x::StaticList, y::StaticList) = first(x) == first(y) ? _iseq(tail(x), tail(y)) : false

Base.in(val, x::StaticList) = _findfirst(==(val), x, slength(x)) !== 0

Base.isempty(::Nil) = true
Base.isempty(::StaticList) = false

Base.empty(::Union{StaticList,ReverseList}) = nil

slength(::Nil) = StaticInt(0)
slength(x::StaticList) = x.length
slength(x::ReverseList) = slength(reverse(x))
@inline Base.length(x::Union{StaticList,Nil,ReverseList}) = Int(slength(x))
Base.size(x::Union{StaticList,Nil}) = (length(x),)

Base.iterate(::Nil) = nothing
Base.iterate(x::Union{StaticList,ReverseList}) = first(x), 2
Base.iterate(::Union{OneItem,ReverseOne}, ::Int) = nothing
@inline Base.iterate(x::TwoItems, s::Int) = s === 2 ? (first(tail(x)), 3) : nothing
@inline function Base.iterate(x::Union{StaticList,ReverseList}, s)
    s > length(x) ? nothing : (@inbounds(x[s]), s + 1)
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

@inline Base.accumulate(op, x::StaticList; init=INIT) = _accum(op, x, init)
@inline _accum(op, x::OneItem, ::Base._InitialValue) = x
@inline _accum(op, x::StaticList, ::Base._InitialValue) = _accum(op, tail(x), first(x))
@inline _accum(op, x::StaticList, init) = __accum(op, x, init, slength(x))
@generated function __accum(op, x::StaticList, init, ::StaticInt{N}) where {N}
    out = Expr(:block, Expr(:meta, :inline))
    push!(out.args, Expr(:(=), :x1, :(op(init, $(_getexpr(:x, 1))))))
    for i in 2:N
        push!(out.args, Expr(:(=), Symbol(:x, i), :(op($(Symbol(:x, i - 1)), $(_getexpr(:x, i))))))
    end
    lst = :nil
    cnt = 1
    for i in N:-1:1
        lst = :(StaticList($(Symbol(:x, i)), $(lst), $(StaticInt(cnt))))
        cnt += 1
    end
    lst = :(StaticList(init, $(lst), $(StaticInt(N + 1))))
    push!(out.args, lst)
    out
end

"""
    insert(list, index, item) -> out

Returns a list where `item` is inserted at `index`. `index` is the index of item in `out`.
"""
@inline function insert(x::StaticList, i::Int, v)
    @boundscheck 1 <= i <= (length(x) + 1) || throw(BoundsError(x, i))
    _insert(x, i, v)
end
@inline _insert(::Nil, ::Int, v) = StaticList(v, nil, ONE)
@inline function _insert(x::StaticList, i::Int, v)
    i === 1 ? assoc(v, x) : assoc(first(x), _insert(tail(x), i - 1, v))
end
insert(x::StaticList, i::StaticInt, v) = _geninsert(x, i, slength(x), v)
@generated function _geninsert(x::StaticList, i::StaticInt{N}, ::StaticInt{L}, v) where {N,L}
    if 1 <= N && N <= (L + 1)
        out = :(StaticList(v, $(ntails_expr(:x, N - 1)), $(StaticInt(L - N + 2))))
        for i in (N-1):-1:1
            out = :(StaticList($(_getexpr(:x, i)), $(out), $(StaticInt(L - i + 2))))
        end
        Expr(:block, Expr(:meta, :inline), out)
    else
        :(throw(BoundsError(x, i)))
    end
end

"""
    deleteat(list, index)

Returns a list without the value corresponding to `index`.
"""
function deleteat(x::StaticList, i::Int)
    @boundscheck checkbounds(x, i)
    _deleteat(x, i)
end
_deleteat(x::OneItem, i::Int) = nil
@inline _deleteat(x::TwoItems, i::Int) = i === 1 ? tail(x) : list(first(x))
@inline function _deleteat(x::StaticList, i::Int)
    i === 1 ? tail(x) : assoc(first(x), _deleteat(tail(x), i - 1))
end
deleteat(x::StaticList, i::StaticInt) = _gendelete(x, i, slength(x))
@generated function _gendelete(x::StaticList, ::StaticInt{N}, ::StaticInt{L}) where {N,L}
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
function popat(x::StaticList, i::Int)
    @boundscheck checkbounds(x, i)
    unsafe_popat(x, i)
end
@inline unsafe_popat(x::OneItem, i::Int) = first(x), nil
@inline function unsafe_popat(x::TwoItems, i::Int)
    i === 1 ? (first(x), tail(x)) : (last(x), list(first(x)))
end
@inline function unsafe_popat(x::StaticList, i::Int)
    if i === 1
        return first(x), tail(x)
    else
        f, t = unsafe_popat(tail(x), i - 1)
        return f, assoc(first(x), t)
    end
end
popat(x::StaticList, i::StaticInt) = _popat(x, i, slength(x))
@generated function _popat(x::StaticList, i::StaticInt{N}, ::StaticInt{L}) where {N,L}
    if 1 <= N && N <= L
        out = ntails_expr(:x, N)
        for i in (N-1):-1:1
            out = :(StaticList($(_getexpr(:x, i)), $(out), $(StaticInt(L - i))))
        end
        Expr(:block, Expr(:meta, :inline), Expr(:tuple, _getexpr(:x, N), out))
    else
        :(throw(BoundsError(x, i)))
    end
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
    _mapfoldr(Base.Fix1(maybe_skip, f), assoc, x, nil, False(), x.length)
end

@noinline function Base.show(io::IO, x::Union{StaticList,Nil,ReverseList})
    show(io, MIME"text/plain"(), x)
end
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

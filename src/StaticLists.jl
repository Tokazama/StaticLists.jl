module StaticLists

using Base: front, tail, isdone
using Base.Iterators: take
using Static

export cons, deleteat, list, insert

@static if isdefined(Base, Symbol("@assume_effects"))
    using Base: @assume_effects
else
    macro assume_effects(_, ex)
        Base.@pure ex
    end
end

@assume_effects :total function _known_instance(T::DataType)
    isdefined(T, :instance) ? getfield(T, :instance) : nothing
end
@inline known_instance(T::DataType) = _known_instance(T)
@inline known_instance(@nospecialize(x)) = _known_instance(typeof(x))

struct Nil end
const nil = Nil()

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

"""
    StaticList(first, tail)

A statically-sized, singly-linked StaticList.
"""
struct StaticList{F,T,L}
    first::F
    tail::T
    length::L
end

const RevList{F,T,L} = Iterators.Reverse{StaticList{F,T,L}}

const EmptyList = Union{StaticList{Nil,Nil,StaticInt{0}},RevList{Nil,Nil,StaticInt{0}}}
const OneItem{T} = StaticList{T,StaticList{Nil,Nil,StaticInt{0}},StaticInt{1}}
const TwoItems{T1,T2} = StaticList{T1,OneItem{T2},StaticInt{2}}
const ThreeItems{T1,T2,T3} = StaticList{T1,TwoItems{T2,T3},StaticInt{3}}
const FourItems{T1,T2,T3,T4} = StaticList{T1,ThreeItems{T2,T3,T4},StaticInt{4}}

const none = StaticList(nil, nil, StaticInt(0))

struct NFirst{P,L}
    parent::P
    length::L
end

const ListType = Union{NFirst,StaticList,RevList}

@generated function _reverse(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :none
    for i in 0:(N - 1)
        out = :(cons(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

# takes the first `N` values and attaches them to the new root/tail
@generated function _reroot(@nospecialize(x0::StaticList), @nospecialize(root::StaticList), ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :root
    for i in (N - 1):-1:0
        out = :(cons(first($(Symbol(:x, i))), $(out)))
    end
    push!(blk.args, out)
    return blk
end

@inline function _reroot(@nospecialize(x0::StaticList), @nospecialize(root::StaticList), N::Int)
    N === 1 ? cons(first(x0), root) : cons(first(x0), _reroot(tail(x), root, N - 1))
end

"""
    list(args...)

Composes a list where each argument is a member of the list.
"""
list() = none
@inline list(@nospecialize(x), @nospecialize(args...)) = cons(x, list(args...))

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

@inline _shrinkbeg(@nospecialize(x::StaticList), N::Int) = N === 1 ? x : _shrinkbeg(tail(x), N - 1)
@generated function _shrinkbeg(@nospecialize(x::StaticList), ::StaticInt{N}) where {N}
    out = :x
    for _ in 1:(N - 1)
        out = :(tail($(out)))
    end
    Expr(:block, Expr(:meta, :inline), out)
end

"""
    insert(list, index, item) -> out

Returns a list where `item` is inserted at `index`. `index` is the index of item in `out`.
"""
@inline function insert(@nospecialize(x::StaticList), @nospecialize(i::Integer), @nospecialize(v))
    @boundscheck 1 <= i <= (length(x) + 1)
    unsafe_insert(x, i, v)
end
@inline unsafe_insert(::EmptyList, ::Int, @nospecialize(v)) = list(v)
@inline function unsafe_insert(@nospecialize(x::OneItem), i::Int, @nospecialize(v))
    i === 1 ? cons(v, x) : list(first(x), v)
end
@inline function unsafe_insert(@nospecialize(x::StaticList), i::Int, @nospecialize(v))
    i === 1 ? cons(v, x) : cons(first(x), unsafe_insert(tail(x), i - 1, v))
end
@generated function unsafe_insert(@nospecialize(x0::StaticList), ::StaticInt{N}, @nospecialize(v)) where {N}
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
function deleteat(@nospecialize(x::StaticList), @nospecialize(i::Integer))
    @boundscheck checkbounds(x, i)
    unsafe_deleteat(x, i)
end
unsafe_deleteat(@nospecialize(x::OneItem), i::Int) = none
@inline function unsafe_deleteat(@nospecialize(x::TwoItems), i::Int)
    i === 1 ? tail(x) : cons(first(x), none)
end
@inline function unsafe_deleteat(@nospecialize(x::StaticList), i::Int)
    i === 1 ? tail(x) : cons(first(x), unsafe_deleteat(tail(x), i - 1))
end
@generated function unsafe_deleteat(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(Base.tail($(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

"""
    StaticLists.popat(StaticList, key) -> (StaticList[key], StaticLists.delete(StaticList, key))

Returns the value at `key` and the StaticList without the value.

!!! warning
    This is not part of the public API and may change without notice.
"""
function popat(@nospecialize(x::StaticList), @nospecialize(i::Integer))
    @boundscheck checkbounds(x, i)
    unsafe_popat(x, i)
end
@inline unsafe_popat(@nospecialize(x::OneItem), i::Int) = first(x), none
@inline function unsafe_popat(@nospecialize(x::TwoItems), i::Int)
    i === 1 ? (first(x), tail(x)) : (last(x), cons(first(x), none))
end
@inline function unsafe_popat(@nospecialize(x::StaticList), i::Int)
    if i === 1
        return first(x), tail(x)
    else
        f, t = unsafe_popat(tail(x), i - 1)
        return f, cons(first(x), t)
    end
end
@generated function unsafe_popat(@nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(Base.tail($(Symbol(:x, N-1))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, :(first($(Symbol(:x, N - 1))), $r))
    return out
end

@generated function unsafe_setindex(@nospecialize(x0::StaticList), @nospecialize(v), ::StaticInt{N}) where {N}
    out = ntails_expr(N)
    r = :(cons(v, Base.tail($(Symbol(:x, N-1)))))
    for i in (N - 2):-1:0
        r = :(cons(first($(Symbol(:x, i))), $r))
    end
    push!(out.args, r)
    return out
end

@generated function _genmap(@nospecialize(f), @nospecialize(x0::StaticList), ::StaticInt{N}) where {N}
    blk = ntails_expr(N)
    out = :none
    for i in (N - 1):-1:0
        out = :(cons(f(first($(Symbol(:x, i)))), $(out)))
    end
    push!(blk.args, out)
    return blk
end
@generated function _mapfoldl(f, op, @nospecialize(x0::StaticList), init::I, ::StaticInt{N}) where {I,N}
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
@generated function _mapfoldr(f, op, @nospecialize(x0::StaticList), init::I, ::StaticInt{N}) where {I,N}
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

@nospecialize

Base.parent(x::StaticList) = x
Base.parent(x::Union{NFirst,RevList}) = getfield(x, 1)

Base.values(x::Union{NFirst,StaticList,RevList}) = x

@inline cons(x, y) = cons(x, StaticList(x, none, StaticInt(1)))
@inline cons(x, ::EmptyList) = StaticList(x, none, StaticInt(1))
@inline cons(x, y::OneItem) = StaticList(x, y, StaticInt(2))
@inline cons(x, y::TwoItems) = StaticList(x, y, StaticInt(3))
@inline cons(x, y::ThreeItems) = StaticList(x, y, StaticInt(4))
@inline cons(x, y::FourItems) = StaticList(x, y, StaticInt(5))
@inline cons(x, y::StaticList) = StaticList(x, y, StaticInt(1) + slength(y))
@inline cons(x::StaticList, y) = unsafe_insert(x, slength(x) + StaticInt(1), y)
@inline cons(x::StaticList, y::StaticList) = cat(x, y)

Base.eltype(x::ListType) = eltype(typeof(x))
Base.eltype(T::Type{<:NFirst}) = eltype(T.parameters[1])
Base.eltype(::Type{EmptyList}) = Union{}
Base.eltype(T::Type{<:OneItem}) = T.parameters[1]
Base.eltype(T::Type{<:StaticList}) = _eltype(slength(T), T)

###
# Indexing
###
Base.checkbounds(x::StaticList, i) = checkbounds(Bool, x, i) ? nothing : throw(BoundsError(x, i))
Base.checkbounds(::Type{Bool}, x::StaticList, i::Integer) = 1 <= i <= slength(x)
function Base.checkbounds(::Type{Bool}, x::StaticList, i::AbstractUnitRange)
    checkbounds(Bool, x, first(x)) && checkbounds(Bool, x, last(x))
end

@inline Base.eachindex(x::StaticList) = Base.OneTo(length(x))

Base.collect(x::RevList) = _reverse(x, slength(x))
Base.collect(x::NFirst) = _reroot(parent(x), none, slength(x))
Base.collect(x::StaticList) = x

Base.getindex(x::StaticList, i::StaticInt) = (@boundscheck checkbounds(x, i); first(_shrinkbeg(x, i)))
Base.getindex(x::ListType, ::Colon) = collect(x)
function Base.getindex(x::ListType, i::Integer)
    @boundscheck checkbounds(parent(x), i)
    return _getindex(parent(x), i)
end
@inline _getindex(x::OneItem, ::Int) = first(x)
@inline _getindex(x::TwoItems, i::Int) = i === 1 ? first(x) : last(x)
@inline function _getindex(x::ThreeItems, i::Int)
    if i === 1
        return first(x)
    elseif i === 2
        return first(tail(x))
    else
        return first(tail(tail(x)))
    end
end
@inline _getindex(x::StaticList, i::Int) = i === 1 ? first(x) : _getindex(tail(x), i - 1)
@inline _getindex(x::StaticList, i::StaticInt) = first(_shrinkbeg(x, i))
@inline Base.get(x::StaticList, i::Integer, d) = checkbounds(Bool, x, i) ? _getindex(x, i) : d

function Base.setindex(x::StaticList, v, i::Integer)
    @boundscheck checkbounds(x, i)
    unsafe_setindex(x, v, i)
end
@inline unsafe_setindex(x::OneItem, v, i::Int) = cons(v, none)
@inline function unsafe_setindex(x::TwoItems, v, i::Int)
    i === 1 ? cons(v, tail(x)) : cons(first(x), v)
end
@inline function unsafe_setindex(x::StaticList, v, i::Int)
    i === 1 ? cons(v, tail(x)) : cons(first(x), unsafe_setindex(tail(x), v, i - 1))
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

slength(T::DataType) = T.parameters[3]()
slength(x::RevList) = slength(parent(x))
slength(x::Union{NFirst,StaticList}) = getfield(x, :length)
@inline Base.length(x::ListType) = Int(slength(x))

###
# Iterators
###
Base.IteratorSize(T::Type{<:ListType}) = Base.HasLength()

Base.Iterators.reverse(x::Union{EmptyList,OneItem}) = x
Base.Iterators.reverse(x::StaticList) = Base.Iterators.Reverse(x)
Base.reverse(x::StaticList) = Base.Iterators.reverse(x)

Base.tail(::EmptyList) = throw(ArgumentError("Cannot call Base.tail on an empty list"))
Base.tail(::OneItem) = none
@inline Base.tail(x::StaticList) = getfield(x, :tail)

Base.front(::EmptyList) = throw(ArgumentError("Cannot call Base.front on an empty list"))
@inline Base.front(::OneItem) = none
@inline Base.front(x::StaticList) = first(x, slength(x) - static(1))

Base.first(::EmptyList) = throw(ArgumentError("Cannot call first on an empty list"))
Base.first(x::StaticList) = getfield(x, :first)
@inline Base.first(x::RevList) = last(parent(x))
Base.first(x::StaticList, i::Integer) = (@boundscheck checkbounds(x, i); NFirst(x, i))
Base.first(x::NFirst, i::Integer) = (@boundscheck checkbounds(x, i); NFirst(parent(x), i))
Base.Iterators.take(x::ListType, i::Integer) = @inbounds first(x, min(i, slength(x)))

Base.last(::EmptyList) = throw(ArgumentError("Cannot call last on an empty list"))
Base.last(x::OneItem) = first(x)
@inline Base.last(x::TwoItems) = first(tail(x))
@inline Base.last(x::StaticList) = @inbounds x[slength(x)]
@inline Base.last(x::RevList) = first(parent(x))
function Base.last(x::StaticList, i::Integer)
    @boundscheck checkbounds(x, i)
    _shrinkbeg(x, (slength(x) + StaticInt(1)) - i)
end

Base.isdone(x::StaticList, s::StaticList) = isempty(s)
Base.iterate(::EmptyList) = nothing
Base.iterate(x::StaticList) = first(x), tail(x)
Base.iterate(::OneItem, state) = nothing
@inline Base.iterate(x::StaticList, s) = isdone(x, s) ? nothing : (first(s), tail(s))
@inline function Base.iterate(x::NFirst, s=(parent(x), length(x)))
    len = getfield(s, 2)
    if len === 0
        return nothing
    else
        lst = getfield(s, 1)
        return first(lst), (tail(lst), len - 1)
    end
end

Base.only(x::OneItem) = first(x)

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

Base.map(f, ::EmptyList) = none
Base.map(f, x::OneItem) = list(f(first(x)))
#@inline Base.map(f, x::TwoItems) = cons(f(first(x)), list(f(last(x))))
@inline Base.map(f, x::StaticList) = _genmap(f, x, slength(x))
@inline Base.mapfoldl(f, op, x::StaticList; init=nil) = _mapfoldl(f, op, x, init, slength(x))
@inline Base.mapfoldr(f, op, x::StaticList; init=nil) = _mapfoldr(f, op, x, init, slength(x))

###
# show
###
Base.show(io::IO, x::Union{StaticList,Nil,NFirst}) = show(io, MIME"text/plain"(), x)
Base.show(io::IO, ::MIME"text/plain", ::Nil) = print(out, "nil")
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

@specialize

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

end

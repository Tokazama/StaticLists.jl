using ArrayInterface
using Base: front, tail
using StaticLists
using StaticLists: pop, popat, popfirst, push, pushfirst
using Static
using Test

lst = StaticList(static(1), static(2), static(3), static(4))
@test values(lst) == lst
@test @inferred(filter(isodd, lst)) == StaticList(static(1), static(3))
@test @inferred(length(lst)) == 4
@test @inferred(ArrayInterface.known_length(typeof(StaticList(1)))) == 1
@test @inferred(ArrayInterface.known_length(lst)) == 4
@test @inferred(ArrayInterface.known_length(typeof(empty(lst)))) == 0
@test @inferred(first(lst)) == 1
@test @inferred(last(lst)) == 4
@test @inferred(tail(lst)) == StaticList(static(2), static(3), static(4))
@test @inferred(front(lst)) == StaticList(static(1), static(2), static(3))
@test @inferred(eltype(lst)) <: StaticInt
@test @inferred(keytype(typeof(lst))) <: Int
@test @inferred(valtype(typeof(StaticList(1)))) <: Int
@test isempty(@inferred(empty(lst)))
@test eltype(typeof(empty(lst))) <: Any
@test !isempty(lst)
@test @inferred(ArrayInterface.known_first(lst)) === static(1)
@test @inferred(ArrayInterface.known_first(typeof(lst))) === static(1)
@test iterate(empty(lst)) === nothing
@test !=(StaticList(1, 2), StaticList(1, 3))
@test !=(StaticList(1, 2), StaticList(1))
@test !=(StaticList(1), StaticList(1, 2))
@test findfirst(==(2), lst) == 2

lst1 = StaticList(1, 2, 3)
@test @inferred(lst1[2]) == 2
@test @inferred(Base.setindex(lst1, 4, 2)) == StaticList(1, 4, 3)

@test @inferred(ArrayInterface.known_length(StaticList())) === 0
@test @inferred(ArrayInterface.known_length(StaticList(1))) === 1
@test @inferred(ArrayInterface.known_length(StaticList(1, 2))) === 2
@test @inferred(ArrayInterface.known_length(StaticList(1, 2, 3))) === 3
lst2 = StaticList(ntuple(static, 40)...)
@test @inferred(ArrayInterface.known_length(lst2)) === 40

lst = StaticList(1, 2, 3, 4)
@test @inferred(ArrayInterface.known_first(lst)) === nothing
@test @inferred(in(4, lst))
@test @inferred(in(5, lst)) === false
@test @inferred(Base.setindex(lst, 6, 3)) == StaticList(1, 2, 6, 4)
@test @inferred(Base.setindex(lst, 6, static(3))) == StaticList(1, 2, 6, 4)
@test @inferred(push(lst, 5)) == StaticList(1, 2, 3, 4, 5)
@test @inferred(pushfirst(lst, 0)) == StaticList(0, 1, 2, 3, 4)
@test @inferred(StaticLists.deleteat(lst, 3)) == StaticList(1, 2, 4)
@test @inferred(StaticLists.deleteat(lst, static(3))) == StaticList(1, 2, 4)
@test @inferred(pop(lst)) == (4, StaticList(1, 2, 3))
@test @inferred(popfirst(lst)) == (1, StaticList(2, 3, 4))
@test @inferred(popat(lst, 3)) == (3, StaticList(1, 2, 4))
@test @inferred(popat(lst, static(3))) == (3, StaticList(1, 2, 4))
@test @inferred(map(i -> i + 1, lst)) == StaticList(2, 3, 4, 5)
inds = keys(lst)
for (i,l) in zip(inds,lst)
    @test i == l
end
@test @inferred(Base.IteratorSize(typeof(lst))) === Base.HasLength()
@test get(lst, 5, nothing) === nothing

kl = KeyedStaticList(StaticList(static(:a), static(:b), static(:c), static(:d)), StaticList(1, 2, 3, 4))
@test @inferred(keytype(kl)) <: StaticSymbol
@test @inferred(keytype(typeof(kl))) <: StaticSymbol
@test @inferred(eltype(kl)) <: Pair{StaticSymbol,Int}
@test @inferred(eltype(typeof(kl))) <: Pair{StaticSymbol,Int}
@test @inferred(valtype(kl)) <: Int
@test @inferred(valtype(typeof(kl))) <: Int
@test @inferred(length(kl)) == 4
@test @inferred(ArrayInterface.known_length(kl)) == 4
@test @inferred(first(kl)) == Pair(static(:a), 1)
@test @inferred(last(kl)) == Pair(static(:d), 4)
@test @inferred(tail(kl)) == KeyedStaticList(StaticList(static(:b), static(:c), static(:d)), StaticList(2, 3, 4))
@test @inferred(front(kl)) == KeyedStaticList(StaticList(static(:a), static(:b), static(:c)), StaticList(1, 2, 3))
@test @inferred(values(kl)) == StaticList(1, 2, 3, 4)
@test @inferred(keys(kl)) == StaticList(:a, :b, :c, :d)
@test @inferred(kl[static(:b)]) == 2
@test kl == KeyedStaticList(:a => 1, :b => 2, :c => 3, :d => 4)
@test @inferred(StaticLists.pop(kl)) == (last(kl), front(kl))
@test @inferred(StaticLists.popfirst(kl)) == (first(kl), tail(kl))
@test @inferred(pushfirst(kl, :z => 0)) == KeyedStaticList(:z => 0, :a => 1, :b => 2, :c => 3, :d => 4)
@test @inferred(push(kl, :e => 5)) == KeyedStaticList(:a => 1, :b => 2, :c => 3, :d => 4, :e => 5)
@test @inferred(StaticLists.deleteat(KeyedStaticList(:a => 1, :b => 2, :c => 3, :d => 4), :c)) == KeyedStaticList(:a => 1, :b => 2, :d => 4)
@test isempty(empty(kl))
for (lst_i,kl_i) = zip(lst, kl)
    @test lst_i == kl_i[2]
end
@test iterate(empty(kl)) === nothing
@test @inferred(ArrayInterface.known_first(KeyedStaticList(StaticList(static(:a)), StaticList(static(1))))) == Pair(static(:a), static(1))
@test @inferred(haskey(kl, :a))

@test @inferred(Base.setindex(kl, 3, static(:b))) == KeyedStaticList(static(:a) => 1, static(:b) => 3, static(:c) => 3, static(:d) => 4)

io = IOBuffer()
show(io, StaticList(1, 2, 3, 4))
str = String(take!(io))
@test str == "StaticList(1, 2, 3, 4)"

io = IOBuffer()
show(io, kl)
str = String(take!(io))
@test str == "KeyedStaticList(static(:a) => 1, static(:b) => 2, static(:c) => 3, static(:d) => 4)"

elst = empty(lst)
@test_throws ArgumentError first(elst)
@test_throws ArgumentError last(elst)
@test_throws ArgumentError tail(elst)
@test_throws ArgumentError front(elst)
@test_throws ArgumentError pop(elst)
@test_throws ArgumentError popat(elst, 0)
@test_throws ArgumentError StaticLists.deleteat(elst, 0)


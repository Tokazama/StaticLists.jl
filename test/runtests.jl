using ArrayInterface
using Base: front, tail
using StaticLists
using StaticLists: pop, popat, popfirst, push, pushfirst
using Static
using Test

lst = List(static(1), static(2), static(3), static(4))
@test values(lst) == lst
@test @inferred(filter(isodd, lst)) == List(static(1), static(3))
@test @inferred(length(lst)) == 4
@test @inferred(ArrayInterface.known_length(typeof(List(1)))) == 1
@test @inferred(ArrayInterface.known_length(lst)) == 4
@test @inferred(ArrayInterface.known_length(typeof(empty(lst)))) == 0
@test @inferred(first(lst)) == 1
@test @inferred(last(lst)) == 4
@test @inferred(tail(lst)) == List(static(2), static(3), static(4))
@test @inferred(front(lst)) == List(static(1), static(2), static(3))
@test @inferred(eltype(lst)) <: StaticInt
@test @inferred(keytype(typeof(lst))) <: Int
@test @inferred(valtype(typeof(List(1)))) <: Int
@test isempty(@inferred(empty(lst)))
@test eltype(typeof(empty(lst))) <: Any
@test !isempty(lst)
@test @inferred(ArrayInterface.known_first(lst)) === static(1)
@test @inferred(ArrayInterface.known_first(typeof(lst))) === static(1)
@test iterate(empty(lst)) === nothing
@test !=(List(1, 2), List(1, 3))
@test !=(List(1, 2), List(1))
@test !=(List(1), List(1, 2))
@test findfirst(==(2), lst) == 2

lst1 = List(1, 2, 3)
@test @inferred(lst1[2]) == 2
@test @inferred(Base.setindex(lst1, 4, 2)) == List(1, 4, 3)

@test @inferred(ArrayInterface.known_length(List())) === 0
@test @inferred(ArrayInterface.known_length(List(1))) === 1
@test @inferred(ArrayInterface.known_length(List(1, 2))) === 2
@test @inferred(ArrayInterface.known_length(List(1, 2, 3))) === 3
lst2 = List(ntuple(static, 40)...)
@test @inferred(ArrayInterface.known_length(lst2)) === 40

lst = List(1, 2, 3, 4)
@test @inferred(ArrayInterface.known_first(lst)) === nothing
@test @inferred(in(4, lst))
@test @inferred(in(5, lst)) === false
@test @inferred(Base.setindex(lst, 6, 3)) == List(1, 2, 6, 4)
@test @inferred(Base.setindex(lst, 6, static(3))) == List(1, 2, 6, 4)
@test @inferred(push(lst, 5)) == List(1, 2, 3, 4, 5)
@test @inferred(pushfirst(lst, 0)) == List(0, 1, 2, 3, 4)
@test @inferred(StaticLists.deleteat(lst, 3)) == List(1, 2, 4)
@test @inferred(StaticLists.deleteat(lst, static(3))) == List(1, 2, 4)
@test @inferred(pop(lst)) == (4, List(1, 2, 3))
@test @inferred(popfirst(lst)) == (1, List(2, 3, 4))
@test @inferred(popat(lst, 3)) == (3, List(1, 2, 4))
@test @inferred(popat(lst, static(3))) == (3, List(1, 2, 4))
@test @inferred(map(i -> i + 1, lst)) == List(2, 3, 4, 5)
inds = keys(lst)
for (i,l) in zip(inds,lst)
    @test i == l
end
@test @inferred(Base.IteratorSize(typeof(lst))) === Base.HasLength()
@test get(lst, 5, nothing) === nothing

kl = KeyedList(List(static(:a), static(:b), static(:c), static(:d)), List(1, 2, 3, 4))
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
@test @inferred(tail(kl)) == KeyedList(List(static(:b), static(:c), static(:d)), List(2, 3, 4))
@test @inferred(front(kl)) == KeyedList(List(static(:a), static(:b), static(:c)), List(1, 2, 3))
@test @inferred(values(kl)) == List(1, 2, 3, 4)
@test @inferred(keys(kl)) == List(:a, :b, :c, :d)
@test @inferred(kl[static(:b)]) == 2
@test kl == KeyedList(:a => 1, :b => 2, :c => 3, :d => 4)
@test @inferred(StaticLists.pop(kl)) == (last(kl), front(kl))
@test @inferred(StaticLists.popfirst(kl)) == (first(kl), tail(kl))
@test @inferred(pushfirst(kl, :z => 0)) == KeyedList(:z => 0, :a => 1, :b => 2, :c => 3, :d => 4)
@test @inferred(push(kl, :e => 5)) == KeyedList(:a => 1, :b => 2, :c => 3, :d => 4, :e => 5)
@test @inferred(StaticLists.deleteat(KeyedList(:a => 1, :b => 2, :c => 3, :d => 4), :c)) == KeyedList(:a => 1, :b => 2, :d => 4)
@test isempty(empty(kl))
for (lst_i,kl_i) = zip(lst, kl)
    @test lst_i == kl_i[2]
end
@test iterate(empty(kl)) === nothing
@test @inferred(ArrayInterface.known_first(KeyedList(List(static(:a)), List(static(1))))) == Pair(static(:a), static(1))
@test @inferred(haskey(kl, :a))

@test @inferred(Base.setindex(kl, 3, static(:b))) == KeyedList(static(:a) => 1, static(:b) => 3, static(:c) => 3, static(:d) => 4)

io = IOBuffer()
show(io, List(1, 2, 3, 4))
str = String(take!(io))
@test str == "List(1, 2, 3, 4)"

io = IOBuffer()
show(io, kl)
str = String(take!(io))
@test str == "KeyedList(static(:a) => 1, static(:b) => 2, static(:c) => 3, static(:d) => 4)"

elst = empty(lst)
@test_throws ArgumentError first(elst)
@test_throws ArgumentError last(elst)
@test_throws ArgumentError tail(elst)
@test_throws ArgumentError front(elst)
@test_throws ArgumentError pop(elst)
@test_throws ArgumentError popat(elst, 0)
@test_throws ArgumentError StaticLists.deleteat(elst, 0)


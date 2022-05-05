using Base: front, tail
using StaticLists
using StaticLists: pop, popat, popfirst, push, pushfirst, deleteat
using Static
using Test

lst = list(static(1), static(2), static(3), static(4))
@test values(lst) == lst
@test @inferred(filter(isodd, lst)) == list(static(1), static(3))
@test @inferred(length(lst)) == 4
@test @inferred(first(lst)) == 1
@test @inferred(last(lst)) == 4
@test last(lst, 3) == list(static(2), static(3), static(4))
@test @inferred(tail(lst)) == list(static(2), static(3), static(4))
@test @inferred(front(lst)) == list(static(1), static(2), static(3))
@test @inferred(eltype(lst)) <: StaticInt
@test @inferred(keytype(typeof(lst))) <: Int
@test @inferred(valtype(typeof(list(1)))) <: Int
@test isempty(@inferred(empty(lst)))
@test eltype(typeof(empty(lst))) <: Union{}
@test !isempty(lst)
@test iterate(empty(lst)) === nothing
@test !=(list(1, 2), list(1, 3))
@test !=(list(1, 2), list(1))
@test !=(list(1), list(1, 2))
@test findfirst(==(2), lst) == 2

lst1 = list(1, 2, 3)
@test @inferred(lst1[2]) == 2
@test @inferred(Base.setindex(lst1, 4, 2)) == list(1, 4, 3)
@test @inferred(reverse(list(1, 2, 3, 4))) == list(4, 3, 2, 1)

lst2 = list(ntuple(static, 40)...)

lst = list(1, 2, 3, 4)
@test @inferred(in(4, lst))
@test @inferred(in(5, lst)) === false
@test @inferred(Base.setindex(lst, 6, 3)) == list(1, 2, 6, 4)
@test @inferred(Base.setindex(lst, 6, static(3))) == list(1, 2, 6, 4)
@test @inferred(push(lst, 5)) == list(1, 2, 3, 4, 5)
@test @inferred(pushfirst(lst, 0)) == list(0, 1, 2, 3, 4)
@test @inferred(deleteat(lst, 3)) == list(1, 2, 4)
@test @inferred(deleteat(lst, static(3))) == list(1, 2, 4)
@test @inferred(pop(lst)) == (4, list(1, 2, 3))
@test @inferred(popfirst(lst)) == (1, list(2, 3, 4))
@test @inferred(popat(lst, 3)) == (3, list(1, 2, 4))
@test @inferred(popat(lst, static(3))) == (3, list(1, 2, 4))
@test @inferred(map(i -> i + 1, lst)) == list(2, 3, 4, 5)

@test foldr(=>, lst) == (1 => (2 => (3 => 4)))
@test foldr(=>, lst; init=0) == (1 => (2 => (3 => (4 => 0))))
@test foldl(=>, lst) == (((1 => 2) => 3) => 4)
@test foldl(=>, lst; init=0) == ((((0 => 1) => 2) => 3) => 4)

inds = keys(lst)
for (i,l) in zip(inds,lst)
    @test i == l
end
@test @inferred(Base.IteratorSize(typeof(lst))) === Base.HasLength()
@test get(lst, 5, nothing) === nothing

kl = KeyedStaticList(list(static(:a), static(:b), static(:c), static(:d)), list(1, 2, 3, 4))
@test @inferred(keytype(kl)) <: StaticSymbol
@test @inferred(keytype(typeof(kl))) <: StaticSymbol
@test @inferred(eltype(kl)) <: Pair{StaticSymbol,Int}
@test @inferred(eltype(typeof(kl))) <: Pair{StaticSymbol,Int}
@test @inferred(valtype(kl)) <: Int
@test @inferred(valtype(typeof(kl))) <: Int
@test @inferred(length(kl)) == 4
@test @inferred(first(kl)) == Pair(static(:a), 1)
@test @inferred(last(kl)) == Pair(static(:d), 4)
@test @inferred(tail(kl)) == KeyedStaticList(list(static(:b), static(:c), static(:d)), list(2, 3, 4))

@test @inferred(front(kl)) == KeyedStaticList(list(static(:a), static(:b), static(:c)), list(1, 2, 3))

@test @inferred(values(kl)) == list(1, 2, 3, 4)
@test @inferred(keys(kl)) == list(:a, :b, :c, :d)
@test @inferred(kl[static(:b)]) == 2
@test kl == KeyedStaticList(:a => 1, :b => 2, :c => 3, :d => 4)
@test @inferred(StaticLists.pop(kl)) == (last(kl), front(kl))
@test @inferred(StaticLists.popfirst(kl)) == (first(kl), tail(kl))
@test @inferred(pushfirst(kl, :z => 0)) == KeyedStaticList(:z => 0, :a => 1, :b => 2, :c => 3, :d => 4)
@test @inferred(push(kl, :e => 5)) == KeyedStaticList(:a => 1, :b => 2, :c => 3, :d => 4, :e => 5)
@test @inferred(deleteat(KeyedStaticList(:a => 1, :b => 2, :c => 3, :d => 4), :c)) == KeyedStaticList(:a => 1, :b => 2, :d => 4)
@test isempty(empty(kl))
for (lst_i,kl_i) = zip(lst, kl)
    @test lst_i == kl_i[2]
end
@test iterate(empty(kl)) === nothing
@test @inferred(haskey(kl, :a))

@test @inferred(Base.setindex(kl, 3, static(:b))) == KeyedStaticList(static(:a) => 1, static(:b) => 3, static(:c) => 3, static(:d) => 4)

io = IOBuffer()
show(io, list(1, 2, 3, 4))
str = String(take!(io))
@test str == "list(1, 2, 3, 4)"

io = IOBuffer()
show(io, kl)
str = String(take!(io))
@test str == "KeyedStaticList(static(:a) => 1, static(:b) => 2, static(:c) => 3, static(:d) => 4)"

elst = empty(lst)
@test_throws ArgumentError first(elst)
@test_throws ArgumentError last(elst)
@test_throws ArgumentError tail(elst)
@test_throws ArgumentError front(elst)


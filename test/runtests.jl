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
@test @inferred(ArrayInterface.known_length(lst)) == 4
@test @inferred(first(lst)) == 1
@test @inferred(last(lst)) == 4
@test @inferred(tail(lst)) == List(static(2), static(3), static(4))
@test @inferred(front(lst)) == List(static(1), static(2), static(3))
@test @inferred(eltype(lst)) <: StaticInt
@test isempty(@inferred(empty(lst)))
@test !isempty(lst)
@test @inferred(ArrayInterface.known_first(lst)) === static(1)

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

kl = KeyedList(List(static(:a), static(:b), static(:c), static(:d)), List(1, 2, 3, 4))
@test @inferred(keytype(kl)) <: StaticSymbol
@test @inferred(valtype(kl)) <: Int
@test @inferred(length(kl)) == 4
@test @inferred(first(kl)) == Pair(static(:a), 1)
@test @inferred(last(kl)) == Pair(static(:d), 4)
@test @inferred(values(kl)) == List(1, 2, 3, 4)
@test @inferred(keys(kl)) == List(:a, :b, :c, :d)
@test @inferred(kl[static(:b)]) == 2

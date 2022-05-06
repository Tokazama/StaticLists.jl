using Base: front, tail
using StaticLists
using StaticLists: popat, to_stacked_index, StackedIndex
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
@test @inferred(insert(lst, 5, 5)) == list(1, 2, 3, 4, 5)
@test @inferred(deleteat(lst, 3)) == list(1, 2, 4)
@test @inferred(deleteat(lst, static(3))) == list(1, 2, 4)
@test @inferred(popat(lst, 3)) == (3, list(1, 2, 4))
@test @inferred(popat(lst, static(3))) == (3, list(1, 2, 4))
@test @inferred(map(i -> i + 1, lst)) == list(2, 3, 4, 5)

@test foldr(=>, lst) == (1 => (2 => (3 => 4)))
@test foldr(=>, lst; init=0) == (1 => (2 => (3 => (4 => 0))))
@test foldl(=>, lst) == (((1 => 2) => 3) => 4)
@test foldl(=>, lst; init=0) == ((((0 => 1) => 2) => 3) => 4)

inds = eachindex(lst)
for (i,l) in zip(inds,lst)
    @test i == l
end
@test @inferred(Base.IteratorSize(typeof(lst))) === Base.HasLength()
@test get(lst, 5, nothing) === nothing

io = IOBuffer()
show(io, list(1, 2, 3, 4))
str = String(take!(io))
@test str == "list(1, 2, 3, 4)"

elst = empty(lst)
@test_throws ArgumentError first(elst)
@test_throws ArgumentError last(elst)
@test_throws ArgumentError tail(elst)
@test_throws ArgumentError front(elst)

# stacked indexing
lens = accumulate(+, list(static(2), static(3), static(4), static(1)))

@test @inferred(to_stacked_index(lens, 1)) === StackedIndex(1, 1)
@test @inferred(to_stacked_index(lens, 2)) === StackedIndex(1, 2)
@test @inferred(to_stacked_index(lens, 3)) === StackedIndex(2, 1)
@test @inferred(to_stacked_index(lens, 4)) === StackedIndex(2, 2)
@test @inferred(to_stacked_index(lens, 5)) === StackedIndex(2, 3)
@test @inferred(to_stacked_index(lens, 6)) === StackedIndex(3, 1)
@test @inferred(to_stacked_index(lens, 7)) === StackedIndex(3, 2)
@test @inferred(to_stacked_index(lens, 8)) === StackedIndex(3, 3)
@test @inferred(to_stacked_index(lens, 9)) === StackedIndex(3, 4)
@test @inferred(to_stacked_index(lens, 10)) === StackedIndex(4, 1)
@test @inferred(to_stacked_index(lens, static(1))) === StackedIndex(static(1), static(1))
@test @inferred(to_stacked_index(lens, static(2))) === StackedIndex(static(1), static(2))
@test @inferred(to_stacked_index(lens, static(3))) === StackedIndex(static(2), static(1))
@test @inferred(to_stacked_index(lens, static(4))) === StackedIndex(static(2), static(2))
@test @inferred(to_stacked_index(lens, static(5))) === StackedIndex(static(2), static(3))
@test @inferred(to_stacked_index(lens, static(6))) === StackedIndex(static(3), static(1))
@test @inferred(to_stacked_index(lens, static(7))) === StackedIndex(static(3), static(2))
@test @inferred(to_stacked_index(lens, static(8))) === StackedIndex(static(3), static(3))
@test @inferred(to_stacked_index(lens, static(9))) === StackedIndex(static(3), static(4))
@test @inferred(to_stacked_index(lens, static(10))) === StackedIndex(static(4), static(1))


using ArrayInterface
using Base: front, tail
using StaticLists
using StaticLists: pop, popat, popfirst, push, pushfirst
using Static
using Test

lst = List(static(1), static(2), static(3), static(4))
@test @inferred(length(lst)) == 4
@test @inferred(ArrayInterface.known_length(lst)) == 4
@test @inferred(first(lst)) == 1
@test @inferred(last(lst)) == 4
@test @inferred(tail(lst)) == List(static(2), static(3), static(4))
@test @inferred(front(lst)) == List(static(1), static(2), static(3))
@test @inferred(eltype(lst)) <: StaticInt

lst = List(1, 2, 3, 4)
@test @inferred(StaticLists.deleteat(lst, 3)) == List(1, 2, 4)
@test @inferred(StaticLists.deleteat(lst, static(3))) == List(1, 2, 4)
@test @inferred(pop(lst)) == (4, List(1, 2, 3))
@test @inferred(popfirst(lst)) == (1, List(2, 3, 4))
@test @inferred(popat(lst, 3)) == (3, List(1, 2, 4))
@test @inferred(popat(lst, static(3))) == (3, List(1, 2, 4))

@testset "StaticLists.jl" begin
    # Write your tests here.
end
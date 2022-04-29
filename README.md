# StaticLists

[![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://Tokazama.github.io/StaticLists.jl/stable)
[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://Tokazama.github.io/StaticLists.jl/dev)
[![Build Status](https://github.com/Tokazama/StaticLists.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/Tokazama/StaticLists.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/Tokazama/StaticLists.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/Tokazama/StaticLists.jl)

This package exports two statically-sized StaticList types, `StaticList` and `KeyedStaticList`.
Similar to Julia's `Tuple` and `NamedTuple`, these types are useful for creating collections of small strongly-typed values.
Unlike `Tuple` and `NamedTuple` , `StaticList` and `KeyedStaticList` may be composed iteratively without having to reconstruct new instances.
This allows small collections (a length of a little over 32) to undergo many operations that may add or remove a few values with little overhead.
Inference is explicitly tested for most methods.
Most methods have also been bench marked using `BenchmarkTools` to ensure there's little to no overhead where possible.

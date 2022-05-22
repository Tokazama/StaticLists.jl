
using Pkg
Pkg.activate(".")
using BenchmarkTools
using Static
using StaticLists

tup = ntuple(+,32)
lst = list(ntuple(+,32)...)
f = Base.Fix2(^, 2);

@btime map(f, $(tup));  # 781.824 ns (13 allocations: 1008 bytes)
@btime map(f, $(lst));  # 95.913 ns (2 allocations: 544 bytes)

@btime accumulate(+, $(tup));  # 14.307 ns (0 allocations: 0 bytes)
@btime accumulate(+, $(lst));  # 13.618 ns (0 allocations: 0 bytes)

@btime Base.setindex($(tup), 100, 30);  # 3.516 ns (0 allocations: 0 bytes)
@btime Base.setindex($(lst), 100, 30);  # 3.749 ns (0 allocations: 0 bytes)

@btime filter(isodd, $(tup));
@btime filter(isodd, $(lst));

@btime filter(isodd, $(tup));
@btime filter(isodd, $(lst));

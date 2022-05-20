
using BenchmarkTools
using Static
using StaticLists

tup = ntuple(+,32)
lst = list(ntuple(+,32)...)

@btime accumulate(+, $(tup));
@btime accumulate(+, $(lst));

@btime Base.setindex($(tup), 100, 30);
@btime Base.setindex($(lst), 100, 30);

@btime filter(isodd, $(tup));
@btime filter(isodd, $(lst));


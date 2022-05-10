
function _precompile_()
    ccall(:jl_generating_output, Cint, ()) == 1 || return nothing

    Base.precompile(Tuple{typeof(Base.eltype),StaticLists.StaticList})
    Base.precompile(Tuple{typeof(Base.first),StaticLists.StaticList})
    Base.precompile(Tuple{typeof(Base.checkbounds),Type{Bool},StaticLists.StaticList,Integer})
    Base.precompile(Tuple{typeof(Base.tail),StaticLists.StaticList})
    Base.precompile(Tuple{typeof(Base.last),StaticLists.StaticList})
    Base.precompile(Tuple{typeof(Base.setindex),StaticLists.StaticList,Any,Integer})
    Base.precompile(Tuple{typeof(StaticLists._setindex),StaticLists.StaticList,Any,Int})
    Base.precompile(Tuple{typeof(Base.getindex),StaticLists.StaticList,Integer})
    Base.precompile(Tuple{typeof(StaticLists._getindex),StaticLists.StaticList,Int})
    Base.precompile(Tuple{typeof(StaticLists._list),Tuple,StaticInt{0}})
    Base.precompile(Tuple{typeof(StaticLists.deleteat),StaticLists.StaticList,Integer})
    Base.precompile(Tuple{typeof(StaticLists.unsafe_deleteat),StaticLists.StaticList,Int})
    Base.precompile(Tuple{typeof(StaticLists.unsafe_deleteat),StaticLists.StaticList,StaticInt})
    Base.precompile(Tuple{typeof(StaticLists.insert),StaticLists.StaticList,Integer,Any})
    Base.precompile(Tuple{typeof(StaticLists.unsafe_insert),StaticLists.StaticList,Int,Any})
    Base.precompile(Tuple{typeof(StaticLists.unsafe_insert),StaticLists.StaticList,StaticInt})
    Base.precompile(Tuple{typeof(StaticLists.popat),StaticLists.StaticList,Integer})
    Base.precompile(Tuple{typeof(StaticLists.unsafe_popat),StaticLists.StaticList,Int})
    Base.precompile(Tuple{typeof(StaticLists.unsafe_popat),StaticLists.StaticList,StaticInt})
    Base.precompile(Tuple{typeof(StaticLists.slength),StaticLists.StaticList})
    Base.precompile(Tuple{typeof(StaticLists.slength),StaticLists.ReverseList})
    Base.precompile(Tuple{typeof(StaticLists.slength),StaticLists.Nil})
    for i in 1:32
        Base.precompile(Tuple{typeof(StaticLists._reverse),StaticLists.StaticList,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._getindex),StaticLists.StaticList,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._list),Tuple,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._setindex),StaticLists.StaticList,Any,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._genmap),Any,StaticLists.StaticList,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._mapfoldl),Any,Any,StaticLists.StaticList,Static.True,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._mapfoldl),Any,Any,StaticLists.StaticList,Static.False,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._mapfoldr),Any,Any,StaticLists.StaticList,Static.True,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._mapfoldr),Any,Any,StaticLists.StaticList,Static.False,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists.__accum),Any,StaticLists.StaticList,Any,StaticInt{i}})
        Base.precompile(Tuple{typeof(StaticLists._findfirst),Function,StaticLists.StaticList,StaticInt{i}})
        for j in 1:i
            Base.precompile(Tuple{typeof(StaticLists._delete),StaticLists.StaticList,StaticInt{j},StaticInt{i}})
            Base.precompile(Tuple{typeof(StaticLists._popat),StaticLists.StaticList,StaticInt{j},StaticInt{i}})
            Base.precompile(Tuple{typeof(StaticLists._insert),StaticLists.StaticList,StaticInt{j},StaticInt{i},Any})
        end
    end
end


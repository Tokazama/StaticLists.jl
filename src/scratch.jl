
#=
#=
    SubList
=#
struct SubList{P,I}
    parent::P
    indices::I
end

subitr(@nospecialize(lst), i::List{True}) = first(lst), (tail(lst), tail(i))
subitr(@nospecialize(lst), i::List{False}) = subitr(tail(lst), tail(i))

Base.iterate(@nospecialize(lst::Sublist)) = subitr(lst.parent, lst.indices)
Base.iterate(@nospecialize(lst::Sublist), ::Tuple{Nil,Nil}) = nothing
Base.iterate(@nospecialize(lst::Sublist), @nospecialize(s)) = @inbounds subitr(s[1], s[2])

_listindices(::StaticInt{1}) = List(True(), nil)
_listindices(::StaticInt{N}) where {N} = List(True(), _listindices(static(N - 1)))
listindices(@nospecialize x::List) = _listindices(ArrayInterface.static_length(x))

list(ntuple(static, Val(known_length(lst)))...)

function static_is_singleton_type(@nospecialize x)
    if Base.issingletontype(x)
        return True()
    else
        return False()
    end
end

@inline function _is_singleton_keys_type(@nospecialize(T::Type{<:KeyedList}))
    static_is_singleton_type(@inbounds(T.parameters[1]))
end
=#


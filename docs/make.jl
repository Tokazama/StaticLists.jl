using StaticLists
using Documenter

DocMeta.setdocmeta!(StaticLists, :DocTestSetup, :(using StaticLists); recursive=true)

makedocs(;
    modules=[StaticLists],
    authors="Zachary P. Christensen <zchristensen7@gmail.com> and contributors",
    repo="https://github.com/Tokazama/StaticLists.jl/blob/{commit}{path}#{line}",
    sitename="StaticLists.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://Tokazama.github.io/StaticLists.jl",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
    ],
)

deploydocs(;
    repo="github.com/Tokazama/StaticLists.jl",
    devbranch="main",
)

# ncmpoly
Usage: include the file to load the stuff and run some examples. Currently,
```julia
julia> include("NCMPoly.jl")
**** starting buchberge on ****
2-element Vector{NCMPoly{AbstractAlgebra.GFElem{Int64}}}:
 u*x*y*x*y*x*y + u*x*y*x*y + u + v
 y*x*y*x*y*x*t + y*x*y*x*t + t + s

obstruction (1, 2): 1, x*t; u*x, 1
g[i] = u*x*y*x*y*x*y + u*x*y*x*y + u + v
g[j] = y*x*y*x*y*x*t + y*x*y*x*t + t + s
S = u*x*s + v*x*t
Sp = u*x*s + v*x*t

obstruction (1, 2): 1, x*y*x*t; u*x*y*x, 1
g[i] = u*x*y*x*y*x*y + u*x*y*x*y + u + v
g[j] = y*x*y*x*y*x*t + y*x*y*x*t + t + s
S = u*x*y*x*s + v*x*y*x*t
Sp = u*x*y*x*s + v*x*y*x*t

obstruction (1, 2): 1, x*y*x*y*x*t; u*x*y*x*y*x, 1
g[i] = u*x*y*x*y*x*y + u*x*y*x*y + u + v
g[j] = y*x*y*x*y*x*t + y*x*y*x*t + t + s
S = u*x*y*x*y*x*s + v*x*y*x*y*x*t
Sp = u*x*y*x*y*x*s + v*x*y*x*y*x*t

done!
5-element Vector{NCMPoly{AbstractAlgebra.GFElem{Int64}}}:
 u*x*y*x*y*x*y + u*x*y*x*y + u + v
 y*x*y*x*y*x*t + y*x*y*x*t + t + s
 u*x*s + v*x*t
 u*x*y*x*s + v*x*y*x*t
 u*x*y*x*y*x*s + v*x*y*x*y*x*t
```


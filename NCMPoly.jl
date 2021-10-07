# following:
# Dissertation
#  Non-Commutative Groebner Bases and Applications
#  Xingqiang Xiu

using AbstractAlgebra

import AbstractAlgebra:
   NCRing,
   NCRingElem,
   Ring,
   RingElement,
   base_ring,
   expressify,
   isone,
   iszero,
   leading_coefficient,
   length,
   one,
   parent,
   zero

###############################################################################
#
# types for multivariates with noncommuting variables
#
###############################################################################

mutable struct NCMPolyRing{T <: RingElement} <: NCRing
   base_ring::Ring
   S::Vector{Symbol}
end

mutable struct NCMPoly{T <: RingElement} <: NCRingElem
   coeffs::Vector{T}
   exps::Vector{Vector{Int}}
   length::Int
   parent::NCMPolyRing{T}
end

struct NCMPolyCoeffs{T <: NCRingElem}
   poly::T
end

struct NCMPolyExponentWords{T <: NCRingElem}
   poly::T
end

struct NCMPolyTerms{T <: NCRingElem}
   poly::T
end

struct NCMPolyMonomials{T <: NCRingElem}
   poly::T
end

###############################################################################
#
# implementation
#
###############################################################################

parent(a::NCMPoly) = a.parent

base_ring(a::NCMPolyRing) = a.base_ring

symbols(a::NCMPolyRing) = a.S

nvars(a::NCMPolyRing) = length(a.S)

length(a::NCMPoly) = a.length

function coefficients(a::NCMPoly{T}) where T
   return NCMPolyCoeffs(a)
end

function exponent_words(a::NCMPoly{T}) where T
   return NCMPolyExponentWords(a)
end

function Base.iterate(x::NCMPolyCoeffs, state = 0)
   state += 1
   if length(x.poly) >= state
      return x.poly.coeffs[state], state
   else
      return nothing
   end
end

function Base.iterate(x::NCMPolyExponentWords, state = 0)
   state += 1
   if length(x.poly) >= state
      return x.poly.exps[state], state
   else
      return nothing
   end
end

function expressify(a::NCMPoly, x = symbols(parent(a)); context = nothing)
   sum = Expr(:call, :+)
   for (c, v) in zip(coefficients(a), exponent_words(a))
      prod = Expr(:call, :*)
      if !isone(c)
         push!(prod.args, expressify(c, context = context))
      end
      j = -1
      e = 0
      for i in v
         if j != i
            if j > 0 && !iszero(e)
               push!(prod.args, e == 1 ? x[j] : Expr(:call, :^, x[j], e))
            end
            e = 0
         end
         j = i
         e += 1
      end
      if j > 0 && !iszero(e)
         push!(prod.args, e == 1 ? x[j] : Expr(:call, :^, x[j], e))
      end
      push!(sum.args, prod)
   end
   return sum
end

@enable_all_show_via_expressify NCMPoly

function expressify(a::NCMPolyRing; context = nothing)
   return Expr(:sequence, Expr(:text, "Free Associative Algebra over "),
                          expressify(base_ring(a)),
                          Expr(:text, " in "),
                          Expr(:series, symbols(a)...))
end

@enable_all_show_via_expressify NCMPolyRing

function zero(a::NCMPolyRing{T}) where T
   return NCMPoly{T}(T[], Vector{Int}[], 0, a)
end

function one(a::NCMPolyRing{T}) where T
   return NCMPoly{T}([one(base_ring(a))], [Int[]], 1, a)   
end

function iszero(a::NCMPoly{T}) where T
   return a.length == 0
end

function isone(a::NCMPoly{T}) where T
   return a.length == 1 && isone(a.coeffs[1]) && isempty(a.exps[1])
end

function gen(a::NCMPolyRing{T}, i::Int) where T
   @assert 0 < i <= nvars(a)
   return NCMPoly{T}([one(base_ring(a))], [Int[i]], 1, a)
end

function gens(a::NCMPolyRing{T}) where {T <: RingElement}
   return [gen(a, i) for i in 1:nvars(a)]
end

function FreeAssociativeAlgebra(R::Ring, s::Vector{String})
   return FreeAssociativeAlgebra(R, map(Symbol, s))
end

function FreeAssociativeAlgebra(R::Ring, s::Vector{Symbol}; cached::Bool = true)
   T = elem_type(R)
   parent_obj = NCMPolyRing{T}(R, s)
   return (parent_obj, gens(parent_obj))
end

function leading_coefficient(a::NCMPoly{T}) where T
   @assert a.length > 0
   return a.coeffs[1]
end

function leading_word(a::NCMPoly{T}) where T
   @assert a.length > 0
   return a.exps[1]
end

function monomial_cmp(a::Vector{Int}, b::Vector{Int})
   if length(a) > length(b)
      return +1
   elseif length(a) < length(b)
      return -1
   else
      # deglex
      for i in 1:length(a)
         if a[i] > b[i]
            return -1
         elseif a[i] < b[i]
            return +1
         end
      end
      return 0
   end
end

function monomial_gt(a::Vector{Int}, b::Vector{Int})
   return monomial_cmp(a, b) > 0
end

function sort_terms!(z::NCMPoly{T}) where T
   p = sortperm(z.exps, lt = monomial_gt)
   z.coeffs = [z.coeffs[p[i]] for i in 1:length(p)]
   z.exps = [z.exps[p[i]] for i in 1:length(p)]
   return z
end

function combine_like_terms!(z::NCMPoly{T}) where T
   o = 0
   i = 1
   while i <= z.length
      if o > 0 && monomial_cmp(z.exps[o], z.exps[i]) == 0
         z.coeffs[o] += z.coeffs[i]
      else
         o += (o < 1 || !iszero(z.coeffs[o]))
         z.exps[o] = z.exps[i]
         z.coeffs[o] = z.coeffs[i]
      end
      i += 1
   end
   o += (o < 1 || !iszero(z.coeffs[o]))
   z.length = o - 1
   return z
end

function (a::NCMPolyRing{T})(b::T) where T
   return NCMPoly(T[b], [Int[]], 1, a)
end

function (a::NCMPolyRing{T})(b::Integer) where T
   return a(base_ring(a)(b))
end

function (a::NCMPolyRing{T})(b::Vector{Int}) where T
   @assert all(i -> (i <= nvars(a)), b)
   return NCMPoly(T[one(base_ring(a))], [b], 1, a)
end

# return c*w*a*wp
function mul_term(c::T, w::Vector{Int}, a::NCMPoly{T}, wp::Vector{Int}) where T
   zcoeffs = isone(c) ? T[a.coeffs[i] for i in 1:a.length] :
                        T[c*a.coeffs[i] for i in 1:a.length]
   zexps = Vector{Int}[vcat(w, a.exps[i], wp) for i in 1:a.length]
   return NCMPoly{T}(zcoeffs, zexps, a.length, parent(a))
end

function Base.:(==)(a::NCMPoly{T}, b::NCMPoly{T}) where T
        return (view(a.coeffs, 1:a.length) == view(b.coeffs, 1:b.length)) && (view(a.exps, 1:a.length) == view(b.exps, 1:b.length)) && (a.length == b.length) && (a.parent == b.parent) # TODO can a.parent == b.parent make problems?
end


# is this worth optimizing with a heap?
function Base.:*(a::NCMPoly{T}, b::NCMPoly{T}) where T
   zcoeffs = T[]
   zexps = Vector{Int}[]
   for i in 1:a.length, j in 1:b.length
      push!(zcoeffs, a.coeffs[i]*b.coeffs[j])
      push!(zexps, vcat(a.exps[i], b.exps[j]))
   end
   z = NCMPoly{T}(zcoeffs, zexps, length(zcoeffs), parent(a))
   return combine_like_terms!(sort_terms!(z))
end

function Base.:+(a::NCMPoly{T}, b::NCMPoly{T}) where T
   zcoeffs = T[]
   zexps = Vector{Int}[]
   i = j = 1
   while i <= a.length && j <= b.length
      c = monomial_cmp(a.exps[i], b.exps[j])
      if c < 0
         push!(zcoeffs, b.coeffs[j])
         push!(zexps, b.exps[j])
         j += 1
      elseif c > 0
         push!(zcoeffs, a.coeffs[i])
         push!(zexps, a.exps[i])
         i += 1
      else
         s = a.coeffs[i] + b.coeffs[j]
         if !iszero(s)
            push!(zcoeffs, s)
            push!(zexps, a.exps[i])
         end
         i += 1
         j += 1
      end
   end
   while i <= a.length
      push!(zcoeffs, a.coeffs[i])
      push!(zexps, a.exps[i])
      i += 1
   end
   while j <= b.length
      push!(zcoeffs, b.coeffs[j])
      push!(zexps, b.exps[j])
      j += 1
   end
   return NCMPoly{T}(zcoeffs, zexps, length(zcoeffs), parent(a))
end

function Base.:-(a::NCMPoly{T}, b::NCMPoly{T}) where T
   zcoeffs = T[]
   zexps = Vector{Int}[]
   i = j = 1
   while i <= a.length && j <= b.length
      c = monomial_cmp(a.exps[i], b.exps[j])
      if c < 0
         push!(zcoeffs, -b.coeffs[j])
         push!(zexps, b.exps[j])
         j += 1
      elseif c > 0
         push!(zcoeffs, a.coeffs[i])
         push!(zexps, a.exps[i])
         i += 1
      else
         s = a.coeffs[i] - b.coeffs[j]
         if !iszero(s)
            push!(zcoeffs, s)
            push!(zexps, a.exps[i])
         end
         i += 1
         j += 1
      end
   end
   while i <= a.length
      push!(zcoeffs, a.coeffs[i])
      push!(zexps, a.exps[i])
      i += 1
   end
   while j <= b.length
      push!(zcoeffs, -b.coeffs[j])
      push!(zexps, b.exps[j])
      j += 1
   end
   return NCMPoly{T}(zcoeffs, zexps, length(zcoeffs), parent(a))
end

function Base.:^(a::NCMPoly{T}, b::Integer) where T
   if b == 0
      return one(parent(a))
   elseif b == 1
      return deepcopy(a)
   elseif a.length == 1
      if isempty(a.exps[1])
         e = [Int[]]
      else
         b < 0 && throw(NotInvertibleError(a))
         e = [reduce(vcat, [a.exps[1] for i in 1:b])]
      end
      return NCMPoly{T}([a.coeffs[1]^b], e, 1, parent(a))
   else
      b < 0 && throw(NotInvertibleError(a))
      return AbstractAlgebra.internal_power(a, b)
   end
end

# return (true, l, r) with a = l*b*r and length(l) minimal
#     or (false, junk, junk)
function monomial_divides(a::Vector{Int}, b::Vector{Int})
   n = length(b)
   for i in 0:length(a)-n
      match = true
      for j in 1:n
         if b[j] != a[i+j]
            match = false
            break
         end
      end
      if match
         return (true, Int[a[k] for k in 1:i],
                       Int[a[k] for k in 1+i+n:length(a)])
      end
   end
   return (false, Int[], Int[])
end

# rem can be optimized with a heap
function rem(f::NCMPoly{T}, g::Vector{NCMPoly{T}}) where T
   R = parent(f)
   s = length(g)
   rcoeffs = T[]
   rexps = Vector{Int}[]
   while length(f) > 0
      i = 1
   @label again
      ok, ml, mr = monomial_divides(f.exps[1], g[i].exps[1])
      if !ok && i < s
         i += 1
         @goto again
      end
      if ok
#         w = NCMPoly{T}(T[one(base_ring(R))], [ml], 1, R)
#         wp = NCMPoly{T}(T[one(base_ring(R))], [mr], 1, R)
#         c = divexact(f.coeffs[1], g[i].coeffs[1])
#         f -= c*w*g[i]*wp
         f -= mul_term(divexact(f.coeffs[1], g[i].coeffs[1]), ml, g[i], mr)
      else
         push!(rcoeffs, f.coeffs[1])
         push!(rexps, f.exps[1])
         f = NCMPoly{T}(f.coeffs[2:end], f.exps[2:end], length(f)-1, R)
      end
   end
   r = NCMPoly{T}(rcoeffs, rexps, length(rcoeffs), R)
   return r
end

function rem_weak(f::NCMPoly{T}, g::Vector{NCMPoly{T}}) where T
   R = parent(f)
   s = length(g)
   while length(f) > 0
      i = 1
   @label again
      ok, ml, mr = monomial_divides(f.exps[1], g[i].exps[1])
      if !ok && i < s
         i += 1
         @goto again
      end
      if ok
#         w = NCMPoly{T}(T[one(base_ring(R))], [ml], 1, R)
#         wp = NCMPoly{T}(T[one(base_ring(R))], [mr], 1, R)
#         c = divexact(f.coeffs[1], g[i].coeffs[1])
#         f -= c*w*g[i]*wp
         f -= mul_term(divexact(f.coeffs[1], g[i].coeffs[1]), ml, g[i], mr)
      else
         break
      end
   end
   return f
end

function interreduce!(g::Vector{NCMPoly{T}}) where T
   s = length(g)
   i = 1
   while length(g) > 1 && length(g) >= i
      r = rem(g[i], g[1:end .!= i])
      if iszero(r)
         deleteat!(g, i)
      else
         g[i] = r
         i = 1
      end 
   end
   return g
end

## checks whether there is an overlap between a and b at position i of b
#  such that b[i:length(b)] = a[1:length(b)-i]
function check_left_overlap(a::Vector{Int}, b::Vector{Int}, i::Int)
   for j in 0:length(b)-i
      if j >= length(a)
         return false # this is a center overlap
      end
      if b[i+j] != a[j+1]
         return false
      end
   end
   return true
end

###
# find all non-trivial left-obstructions of a and b
# i.e. all words w_1 and w_2^' s.t. w_1 a = b w_2^'
# where length(w_1) < length(b) and length(w_2^') < length(a)
# the return vector is of the form [(w_1, w_2^'), ...]
# if w_1 or w_2^' is empty, the corresponding obstruction is not returned
function left_obstructions(a::Vector{Int}, b::Vector{Int})
   v = Tuple{Vector{Int}, Vector{Int}}[];
   for i in 2:length(b)
      if check_left_overlap(a, b, i)
         if length(b)-i + 2 <= length(a) # w_2^' should not be empty!
            push!(v, (b[1:i-1], a[length(b)-i + 2:length(a)]))
         end
      end
   end
   return v
end


###
# find all non-trivial right-obstructions of a and b
# i.e. all words w_2 and w_1^' s.t. a w_1^' = w_2 b
# where length(w_1^') < length(b) and length(w_2) < length(a)
# the return vector is of the form [(w_2, w_1^'), ...]
# if w_1^' or w_2 is empty, the corresponding obstruction is not returned
function right_obstructions(a::Vector{Int}, b::Vector{Int})
   return left_obstructions(b, a)
end

###
# check, whether a is a true subword of b at index i
function check_centre_overlap(a::Vector{Int}, b::Vector{Int}, i::Int)
   for j in 1:length(a)
      if i+j -1 > length(b)
         return false
      end
      if a[j] != b[i + j - 1]
         return false
      end
   end
   return true
end

function centre_obstructions_first_in_second(a::Vector{Int}, b::Vector{Int})
   v = Tuple{Vector{Int}, Vector{Int}}[]
   for i in 1:length(b)
      if check_centre_overlap(a, b, i)
         push!(v, (b[1:i-1], b[i + length(a): length(b)]))
      end
   end
   return v
end

##
# return all centre obstructions of a and b, i.e. all (w_i, w_i^')
# such that either
# w_i a w_i^' = b
# or
# w_i b w_i^' = a
# either or both of w_i and w_i^' can be empty
function centre_obstructions(a::Vector{Int}, b::Vector{Int})
   if length(a) > length(b)
      return centre_obstructions_first_in_second(b, a)
   else
      return centre_obstructions_first_in_second(a, b)
   end
end

# all non-trivial ones
function obstructions(a::Vector{Int}, b::Vector{Int})
   one = Int[] # the empty word
   res = Tuple{Vector{Int}, Vector{Int}, Vector{Int}, Vector{Int}}[]
   for x in centre_obstructions_first_in_second(b, a)
      push!(res, (one, one, x[1], x[2]))
   end
   for x in centre_obstructions_first_in_second(a, b)
      push!(res, (x[1], x[2], one, one))
   end
   for x in left_obstructions(a, b)
      push!(res, (x[1], one, one, x[2]))
   end
   for x in left_obstructions(b, a)
      push!(res, (one, x[2], x[1], one))
   end
   for x in res
      @assert vcat(x[1], a, x[2]) == vcat(x[3], b, x[4])
   end
   return res
end

# all non-trivial self obstructions
function obstructions(a::Vector{Int})
   one = Int[] # the empty word
   res = Tuple{Vector{Int}, Vector{Int}, Vector{Int}, Vector{Int}}[]
   for x in left_obstructions(a, a)
      push!(res, (one, x[2], x[1], one))
   end
   for x in res
      @assert vcat(x[1], a, x[2]) == vcat(x[3], a, x[4])
   end
   return res   
end

# theorem 4.1.14
function buchberger(g::Vector{NCMPoly{T}}) where T

println("**** starting buchberge on ****")
show(stdout, "text/plain", g)
println()

   g = copy(g)
   R = parent(g[1])
   dummy_obstr = (Int[], Int[], Int[], Int[])
   empty_obstr_set = typeof(dummy_obstr)[]

# step 1
   s = length(g)
   B = typeof(empty_obstr_set)[
            if i > j
               empty_obstr_set
            elseif i == j
               obstructions(leading_word(g[i]))
            else
               obstructions(leading_word(g[i]), leading_word(g[j]))
            end
         for i in 1:s, j in 1:s]

@label step2
   @assert s == length(g)
   i = j = 0
   o = dummy_obstr
   # check all entries with i <= j
   for jj in 1:s, ii in 1:jj
      if !isempty(B[ii, jj])
         (i, j) = (ii, jj)
         o = popfirst!(B[i, j])
         break
      end
   end
   if !(i > 0 && j > 0)
println("\ndone!")
      # B is empty
      return g
   end

# step3
println("\nobstruction ", (i, j), ": ", R(o[1]), ", ", R(o[2]),
                                  "; ", R(o[3]), ", ", R(o[4]))
@show g[i]
@show g[j]
   S = mul_term(inv(leading_coefficient(g[i])), o[1], g[i], o[2]) -
       mul_term(inv(leading_coefficient(g[j])), o[3], g[j], o[4])
@show S
   Sp = rem(S, g) # or rem_weak
@show Sp
   if iszero(Sp)
      @goto step2
   end

# step4
   s += 1
   push!(g, Sp)
   # julia doesn't have a matrix resize!, so make a new matrix :(
   B = typeof(empty_obstr_set)[
            if i < s && j < s
               # copy old entry
               B[i, j]
            elseif i > j
               empty_obstr_set
            elseif i == j
               obstructions(leading_word(g[i]))
            else
               obstructions(leading_word(g[i]), leading_word(g[j]))
            end
         for i in 1:s, j in 1:s]
   @goto step2
end

###############################################################################
#
# examples/tests
#
###############################################################################

#=
function debug_obstructions(a::Vector{Int}...)
   println()
   println("obstructions ", a)
   show(stdout, "text/plain", obstructions(a...))
   println()
end

debug_obstructions(Int[1,2,3], Int[2])
debug_obstructions(Int[1,2,3], Int[2,3])
debug_obstructions(Int[1,2], Int[2,3])
debug_obstructions(Int[1,2,1])
=#


# example 4.1.15 continued:
#  typo1: the last member of O(1,2) is o_{1,2}(1, (x*y)^2*x*t; u*(x*y)^2*x, 1)
#  typo2: g2 = u*(x*y)^3 + u*(x*y)^2 + u + v
R, (x, y, u, v, t, s) = FreeAssociativeAlgebra(GF(2), ["x", "y", "u", "v", "t", "s"])
g = buchberger([u*(x*y)^3 + u*(x*y)^2 + u + v,
                (y*x)^3*t + (y*x)^2*t + t + s])
show(stdout, "text/plain", g)
println()

nothing

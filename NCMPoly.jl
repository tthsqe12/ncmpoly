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
   elem_type,
   expressify,
   isone,
   iszero,
   leading_coefficient,
   length,
   one,
   parent,
   parent_type,
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

parent_type(::Type{NCMPoly{T}}) where T = NCMPolyRing{T}

elem_type(::Type{NCMPolyRing{T}}) where T = NCMPoly{T}

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

#@enable_all_show_via_expressify NCMPoly

function expressify(a::NCMPolyRing; context = nothing)
   return Expr(:sequence, Expr(:text, "Free Associative Algebra over "),
                          expressify(base_ring(a)),
                          Expr(:text, " in "),
                          Expr(:series, symbols(a)...))
end

#@enable_all_show_via_expressify NCMPolyRing

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

function deg(a::NCMPoly{T}) where T
        if a.length > 0
                return length(leading_word(a))
        else
                return 0
        end
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


# check whether w_2 = v w_1 for some word v
function issubwordright(w_1::Vector{Int}, w_2::Vector{Int})
        if length(w_1) > length(w_2)
                return false
        end
        for i in 0:length(w_1) - 1
                if w_1[length(w_1) - i] != w_2[length(w_2) - i]
                        return false
                end
        end
        return true
end


# check whether w_2 = w_1 v for some word v
function issubwordleft(w_1::Vector{Int}, w_2::Vector{Int})
        if length(w_1) > length(w_2)
                return false
        end

        for i in 1:length(w_1)
                if w_1[i] != w_2[i]
                        return false
                end
        end
        return true
end


###
# check if for obs1 = (w_i, w_i^'; u_j, u_j^') and obs2 = (w_k, w_k^'; v_l, v_l^') 
# it holds that u_j == w v_l and u_j^' = v_l^' w^' for some w, w^'
# i.e. if obs2 is a subobstruction of obs1
# both w and w^' might be empty
function issubobstruction(obs1::NTuple{4, Vector{Int}}, obs2::NTuple{4, Vector{Int}})
#        if length(obs2[3]) > length(obs1[3]) || length(obs2[4]) > length(obs1[4])
#                return false
#        end
        if issubwordright(obs2[3], obs1[3]) && issubwordleft(obs2[4], obs1[4]) 
                return true
        else
                return false
        end
end

# check whether there exists a w^'' such that
# w1 LM(g1) w2 = w1 LM(g1) w^'' LM(g2) u2
function hasoverlap(g1, g2, w1, w2, u1, u2)
        lw1 = leading_word(g1)
        lw2 = leading_word(g2)
        concatenated_word = vcat(w1, lw1, w2)
        for i in 1:length(w1)
                c = popfirst!(concatenated_word)
                @assert c == w1[i]
        end
        for i in 1:length(lw1)
                c = popfirst!(concatenated_word)
                @assert c == lw1[i]
        end
        for j in 0:length(u2)-1
                c = pop!(concatenated_word)
                @assert c = u2[length(u2)-j]
        end
        if length(concatenated_word) < length(lw2)
                return false
        end
        return issubwordright(lw2, concatenated_word) # TODO maybe just comparing lengths should be sufficient
end

function isredundant(obs::NTuple{4, Vector{Int}}, obs_index::Int, s::Int, B::Matrix{Vector{NTuple{4, Vector{Int}}}})
        # cases 4b + 4c
        for j in 1:size(B)[1]
                for k in 1:length(B[j, s])
                        if issubobstruction(obs, B[j, s][k])
                                # case 4b
                                if length(obs[3]) - length(B[j, s][k][3]) + length(obs[4]) - length(B[j,s][k][4]) > 0
                                        return true
                                # case 4c        
                                elseif obs_index > j 
                                        return true
                                elseif obs_index == j && length(obs[3]) - length(B[j, s][k][3]) + length(obs[4]) - length(B[j,s][k][4]) == 0 && monomial_gt(obs[1], B[j, s][k][1])
                                        return true
                                end
                        end
                end
        end
        # case 4d
        # size(B) should be (s, s)
        # we want to iterate over all B[i, obs_index] with i < s
        for i in 1:size(B)[1]-1 
                for k in 1:length(B[i, obs_index])
                        if issubwordright(B[i, obs_index][k][3], obs[1]) && issubwordleft(B[i, obs_index][k][4], obs[2])
                                show(obs)
                                show(B[i, obs_index][k])
                                u1 = copy(obs[1])
                                u2 = copy(obs[2])
                                v1 = copy(B[i, obs_index][k][3])
                                v2 = copy(B[i, obs_index][k][4])
                                for i in 1:length(v1)
                                        pop!(u1)
                                end
                                for j in 1:length(v2)
                                        popfirst!(u2)
                                end
                                @assert monomial_cmp(vcat(u1, v1), obs[1]) == 0
                                @assert monomial_cmp(vcat(v2, u2), obs[2]) == 0
                                if !hasoverlap(g[i], g[s], vcat(u1, B[i, obs_index][k][1]), vcat(B[i, obs_index][k][2], u2), obs[3], obs[4]) 
                                        return true
                                end
                        end
                end
        end
        return false
end

## s is the index of the newly added layer of obstructions in B
function remove_redundancies!(B::Matrix{Vector{NTuple{4, Vector{Int}}}}, s::Int, g::Vector{NCMPoly{T}}) where T
        del_counter = 0
        for i in 1:s
                k = 1
                while k <= length(B[i, s])
                        if isredundant(B[i, s][k], i, s, B)
                                deleteat(B[i, s][k])
                                del_counter += 1
                        else 
                                k += 1
                        end
                end
        end
        # TODO case 4e from Thm 4.1 in Kreuzer Xiu
end

function get_obstructions(g::Vector{NCMPoly{T}}, s::Int) where T
        dummy_obstr = (Int[], Int[], Int[], Int[])
        empty_obstr_set = typeof(dummy_obstr)[]
        new_B = typeof(empty_obstr_set)[
                    if i > j
                       empty_obstr_set
                    elseif i == j
                       obstructions(leading_word(g[i]))
                    else
                       obstructions(leading_word(g[i]), leading_word(g[j]))
                    end
                 for i in 1:s, j in 1:s]
        obstr_count = 0
        for i in 1:s, j in 1:s
                obstr_count += length(new_B[i,j])
        end
        # TODO maybe here some redundancies can be removed too, check Kreuzer Xiu
        println("$obstr_count many obstructions")
        return new_B

end


function add_obstructions(g::Vector{NCMPoly{T}}, B::Matrix{Vector{NTuple{4, Vector{Int64}}}}, s::Int) where T
        dummy_obstr = (Int[], Int[], Int[], Int[])
        empty_obstr_set = typeof(dummy_obstr)[]
        new_B = Vector{NTuple{4, Vector{Int64}}}[
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
        remove_redundancies!(new_B, s, g)
        return new_B
end


function buchberger(g::Vector{NCMPoly{T}}, degbound = typemax(Int)::Int) where T

println("**** starting buchberger ****")
#show(stdout, "text/plain", g)
println()

   g = copy(g)
   R = parent(g[1])
   checked_obstructions = 0
# step 1
   s = length(g)
   dummy_obstr = (Int[], Int[], Int[], Int[])
   empty_obstr_set = typeof(dummy_obstr)[]

   B = get_obstructions(g, s)
   while true
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
        #println("\nobstruction ", (i, j), ": ", R(o[1]), ", ", R(o[2]),
        #                                  "; ", R(o[3]), ", ", R(o[4]))
        #@show g[i]
        #@show g[j]
           S = mul_term(inv(leading_coefficient(g[i])), o[1], g[i], o[2]) -
               mul_term(inv(leading_coefficient(g[j])), o[3], g[j], o[4])
        #@show S
           Sp = rem(S, g) # or rem_weak
           checked_obstructions += 1
           if checked_obstructions % 5000 == 0
                   println("checked $checked_obstructions obstructions")
           end
        #@show Sp
           if iszero(Sp) || deg(Sp) > degbound
                   continue
           end

        # step4
           s += 1
           push!(g, Sp)
           # julia doesn't have a matrix resize!, so make a new matrix :(
           println("adding new obstructions! checked $checked_obstructions so far")
           B = add_obstructions(g, B, s)
   end
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
#R, (x, y, u, v, t, s) = FreeAssociativeAlgebra(GF(2), ["x", "y", "u", "v", "t", "s"])
#g = buchberger([u*(x*y)^3 + u*(x*y)^2 + u + v,
#                (y*x)^3*t + (y*x)^2*t + t + s])
#show(stdout, "text/plain", g)
#println()

nothing

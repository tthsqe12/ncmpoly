include("NCMPoly.jl")


function free_alg_for_graph(basering::Ring, adj::Matrix{Int})
        (n, ncols) = size(adj)
        @assert n == ncols
        generator_strings = String[]
        for i in 1:n, j in 1:n
                push!(generator_strings, "u[$i,$j]")
        end
        A, g = FreeAssociativeAlgebra(basering, generator_strings)
        u = Matrix{elem_type(A)}(undef, n, n)
        for i in 1:n, j in 1:n
                u[i, j] = g[(i-1)*size(adj)[2] + j]
        end
        relations = elem_type(A)[]
        for i in 1:n, j in 1:n
                push!(relations, u[i, j] * u[i, j] - u[i, j])
                for k in 1:n
                        if k != j
                                if !(u[i,j]*u[i,k] in relations)
                                        push!(relations, u[i, j]*u[i, k])
                                end
                                if !(u[j,i]*u[k,i] in relations)
                                        push!(relations, u[j, i]*u[k, i])
                                end
                                for l in 1:n
                                        if adj[i, k] != adj[j, l] && !( u[i, j]*u[k, l] in relations)
                                                push!(relations, u[i, j]*u[k, l])
                                        end
                                end
                        end
                end
        end
        sum_1 = zero(A)
        sum_2 = zero(A)
        for i in 1:n
                for k in 1:n
                        sum_1 += u[i, k]
                        sum_2 += u[k, i]
                end
                if !(sum_1 - one(A) in relations)
                        push!(relations, sum_1 - one(A))
                end
                if !(sum_2 - one(A) in relations)
                        push!(relations, sum_2 - one(A))
                end
                sum_1 = zero(A)
                sum_2 = zero(A)
        end
        return A, u, relations
end

function check_commutativity(u::Matrix{NCMPoly{Rational{BigInt}}}, gb::Vector{NCMPoly{Rational{BigInt}}}, A::NCMPolyRing{Rational{BigInt}})
        for i in 1:size(u)[1]
                for j in 1:size(u)[2]
                        for k in 1:size(u)[1]
                                for l in 1:size(u)[2]
                                        if !iszero(rem(u[i, j]*u[k, l] - u[k, l] * u[i, j], gb))
                                                return false
                                        end
                                end
                        end
                end
        end
        return true
end

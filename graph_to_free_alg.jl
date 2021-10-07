include("NCMPoly.jl")


function free_alg_for_graph(adj::Matrix{Int})
#        @assert size(adj)[1] = size(adj)[2]
        generator_strings = String[];
        for i in 1:size(adj)[1]
                for j in 1:size(adj)[2]
                        push!(generator_strings, "u_$i,$j")
                end
        end
        A, g = FreeAssociativeAlgebra(QQ, generator_strings);
        u = Matrix{NCMPoly{Rational{BigInt}}}(undef, size(adj)[1], size(adj)[2]);
        for i in 1:size(adj)[1]
                for j in 1:size(adj)[2]
                        u[i, j] = g[(i-1)*size(adj)[2] + j];
                end
        end
        relations = NCMPoly{Rational{BigInt}}[];
        for i in 1:size(adj)[1]
                for j in 1:size(adj)[2]
                        push!(relations, u[i, j] * u[i, j] - u[i, j]);
                        for k in 1:size(adj)[1]
                                if k != j
                                        push!(relations, u[i, j]*u[i, k]);
                                        push!(relations, u[j, i]*u[k, i]);
                                end
                                for l in 1:size(adj)[2]
                                        if adj[i, k] != adj[j, l]
                                                push!(relations, u[i, j]*u[k, l]);
                                                push!(relations, u[k, l]*u[i, j]);
                                        end
                                end
                        end
                end
        end
        sum_1 = zero(A);
        sum_2 = zero(A);
        for i in 1:size(adj)[1]
                for k in 1:size(adj)[1]
                        sum_1 += u[i, k]
                        sum_2 += u[k, i]
                end
                push!(relations, sum_1 - one(A));
                push!(relations, sum_2 - one(A));
        sum_1 = zero(A);
        sum_2 = zero(A);
        end
        b = buchberger(relations)

        return b, u, A
end

function check_commutativity(u::Matrix{NCMPoly{Rational{BigInt}}}, gb::Vector{NCMPoly{Rational{BigInt}}}, A::NCMPolyRing{Rational{BigInt}})
        for i in 1:size(u)[1]
                for j in 1:size(u)[2]
                        for k in 1:size(u)[1]
                                for l in 1:size(u)[2]
                                        if iszero(rem(u[i, j]*u[k, l] - u[k, l] * u[i, j], gb))
                                                return false
                                        end
                                end
                        end
                end
        end
        return true
end

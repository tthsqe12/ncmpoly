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
                        sum_i = zero(A);
                        sum_j = zero(A);
                        for k in 1:size(adj)[1]
                                sum_i += u[i, k];
                                sum_j += u[k, j];
                        end
                        push!(relations, sum_i - one(A));
                        push!(relations, sum_j - one(A));
                        for k in 1:size(adj)[1]
                                if k != j
                                        push!(relations, u[i, j]*u[i, k]);
                                        push!(relations, u[j, i]*u[k, i]);
                                end
                                for l in 1:size(adj)[2]
                                        if adj[i, j] != adj[k, l]
                                                push!(relations, u[i, j]*u[k, l]);
                                                push!(relations, u[k, l]*u[i, j]);
                                        end
                                end
                        end
                end
        end
        b = buchberger(relations)
        return b
end

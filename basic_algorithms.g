DeclareGlobalFunction( "AverageTheGeneratingFunction" );
InstallGlobalFunction(AverageTheGeneratingFunction, function(cyclotomic_order, polynomial_powers)
    local all_e_powers, base_power, generating_product, p, sum_aggregate;

    all_e_powers := List([0..cyclotomic_order],x->E(cyclotomic_order) ^ x);
    # ^^^^ We cache all the roots of unity so they don't need to be recalculated every time.
    sum_aggregate := 0;

    for base_power in [1..cyclotomic_order] do
        # Now we evaluate the generating function one multiplication bracket at a time:
        generating_product := 1;
        for p in polynomial_powers do
            generating_product := generating_product + generating_product * all_e_powers[(p * base_power) mod cyclotomic_order + 1];
        od;
        sum_aggregate := sum_aggregate + generating_product;
        # Print(base_power, "\n");
    od;
    return sum_aggregate / cyclotomic_order;
end);

DeclareGlobalFunction( "OneDimensionalUpperBound" );
InstallGlobalFunction(OneDimensionalUpperBound, function(elements, weights)
    # This is the interface function for the algorithm using the 1-dimensional generating function.
    local cyclotomic_order, n, p, permutation_of_elements, powers;

    n := Length(elements);
    # Input check:
    if n <> Length(weights) then
        Error("Elements and Weights must have the same length!");
        return fail;
    fi;
    # We create all the powers that are within the generating polynomial:
    powers := [];
    for permutation_of_elements in SymmetricGroup(n) do
        Add(powers, ScalarProduct(weights, Permuted(elements, permutation_of_elements)));
    od;
    cyclotomic_order := Sum(elements) * Sum(weights);
    return AverageTheGeneratingFunction(cyclotomic_order, powers);
end);

DeclareGlobalFunction( "CoefficientList" );
InstallGlobalFunction(CoefficientList, function(cyc_order, powers)
    local former_chunk, latter_chunk, list_length, p, vec_coeffs_forward, vec_coeffs_backward;

    list_length := Length(powers);

    vec_coeffs_forward := ListWithIdenticalEntries(cyc_order, 0);
    vec_coeffs_forward[1] := 1;
    for p in powers{[1..list_length / 2]} do
        # This is what multiplying by (1+x^p) does to the coefficients:
        latter_chunk := vec_coeffs_forward{[1..cyc_order-p]};
        vec_coeffs_forward{[1..p]} := vec_coeffs_forward{[1..p]} + vec_coeffs_forward{[cyc_order-p+1..cyc_order]};
        vec_coeffs_forward{[p+1..cyc_order]} := vec_coeffs_forward{[p+1..cyc_order]} + latter_chunk;
        # Print(p, "\n");
    od;
    # We stop halfway in to save on (not too much!) memory with the huge numbers, and go "backwards":
    vec_coeffs_backward := ListWithIdenticalEntries(cyc_order, 0);
    vec_coeffs_backward[1] := 1;
    for p in powers{[list_length / 2 + 1..list_length]} do
        # This is what multiplying by (1+x^p) does to the coefficients !!but when going backwards!! to use scalar product at the end:
        former_chunk := vec_coeffs_backward{[p+1..cyc_order]};
        vec_coeffs_backward{[cyc_order-p+1..cyc_order]} := vec_coeffs_backward{[cyc_order-p+1..cyc_order]} + vec_coeffs_backward{[1..p]};
        vec_coeffs_backward{[1..cyc_order-p]} := vec_coeffs_backward{[1..cyc_order-p]} + former_chunk;
        # Print(p, "\n");
    od;
    # Then we can collect the contributions wiht a scalar product:
    return ScalarProduct(vec_coeffs_forward, vec_coeffs_backward);
end);

DeclareGlobalFunction( "InterfaceVectors" );
InstallGlobalFunction(InterfaceVectors, function(elements, weights)
    # This is the interface function for the algorithm using long lists of coefficients, expanding the generating function that way.
    local cyclotomic_order, n, p, permutation_of_elements, powers;

    n := Length(elements);
    if n <> Length(weights) then
        Error("Elements and Weights must have the same length!");
        return fail;
    fi;
    # We create all the powers that are within the generating polynomial:
    powers := [];
    for permutation_of_elements in SymmetricGroup(n) do
        Add(powers, ScalarProduct(weights, Permuted(elements, permutation_of_elements)));
    od;
    # Print(Length(Unique(powers)), "\n");
    cyclotomic_order := Sum(elements) * Sum(weights);
    return CoefficientList(cyclotomic_order, powers);
end);

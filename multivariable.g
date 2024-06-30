DeclareGlobalFunction( "FourObjectBound" );
InstallGlobalFunction(FourLighterCharacters, function(weights)
    local all_e_powers, cyclo_power, g, weights_permuted, cyclotomic_order, powers_permutation, powers_base, sum_aggregate, this_summand, together, w, x, y;

    weights_permuted := [];
    for g in SymmetricGroup(4) do
        Add(weights_permuted, Permuted(weights, g));
    od;
    cyclotomic_order := Sum(weights);
    all_e_powers := List([0..cyclotomic_order],x->E(cyclotomic_order) ^ x);
    # ^^^^ We cache all the roots of unity so they don't need to be recalculated every time.
    powers_base := [1 .. cyclotomic_order];
    sum_aggregate := 0;
    for w in powers_base do
        Print(w, "\n");
        for x in powers_base do
            for y in powers_base do
                # Utilising the fact that we only take the lists with sum being 0 mod(cyclotomic_order).
                together := [w, x, y, (cyclotomic_order - w - x - y) mod cyclotomic_order];
                # Now we evaluate the generating function one multiplication bracket at a time:
                this_summand := 1;
                for powers_permutation in weights_permuted do
                    cyclo_power := ScalarProduct(powers_permutation, together) mod cyclotomic_order;
                    this_summand := this_summand + this_summand * all_e_powers[cyclo_power + 1];
                od;
                sum_aggregate := sum_aggregate + this_summand;
            od;
        od;
    od;
    return sum_aggregate / cyclotomic_order^(Length(weights) - 1);
end);

DeclareGlobalFunction( "FasterFourObject" );
InstallGlobalFunction(FasterFourObject, function(weights)
    local all_e_powers, all_factorials, all_permutations, all_tuples, current_3_tuple, cyclotomic_order, full_4_tuple, last_coordinate, n, n_factorial, power, sum_aggregate, value_of_gen_function, zeta_powers;

    n := Length(weights);
    if n <> 4 then
        Print("WARNING!!\nThis function is not meant to handle inputs of length different from 4.\nComputation may take VERY long!");
    fi;
    # Precompute important values:
    n_factorial := Factorial(n);
    all_factorials := List([1..n],Factorial);
    all_permutations := TransposedMat(Arrangements(weights,n));
    cyclotomic_order := Sum(weights);
    all_e_powers := List([0..cyclotomic_order - 1], x->E(cyclotomic_order) ^ x);
    # ^^^^ We cache all the roots of unity so they don't need to be recalculated every time.

    Display(["start",StringTime(Runtime())]);
    all_tuples := UnorderedTuples([0..cyclotomic_order-1],n-1);
    Display(["tup",StringTime(Runtime())]);

    sum_aggregate := 0;
    for current_3_tuple in all_tuples do
        last_coordinate := (-Sum(current_3_tuple)) mod cyclotomic_order;
        # We only continue if the last coordinate is the biggest, because permutations do not change the value.
        if last_coordinate >= current_3_tuple[n-1] then
            full_4_tuple := Concatenation(current_3_tuple,[last_coordinate]);
            value_of_gen_function := cyclotomic_order * n_factorial / Product(Collected(full_4_tuple), x->all_factorials[x[2]]);
            zeta_powers := (full_4_tuple*all_permutations mod cyclotomic_order)+1;
            for power in zeta_powers do
                value_of_gen_function := value_of_gen_function + value_of_gen_function * all_e_powers[power];
            od;
            sum_aggregate := sum_aggregate + value_of_gen_function;
        fi;
    od;
    Display(["finish",StringTime(Runtime())]);
    return sum_aggregate/cyclotomic_order^n;
end);

DeclareGlobalFunction( "FiveObjectBound" );
InstallGlobalFunction(FiveObjectBound, function(weights)
    local all_e_powers, coeffs_cyc_sum, mod_s_inverses, matrix_of_weight_perms, cyclotomic_order,
    final_result, inverting_element, inv_x, inv_y, inv_z, inv_last, is_minimal, last_coordinate, multiplier, 
    new_used_tuple, p_minus_1, start, this_permutation, this_summand, together, used_tuple, x, y, z;

    cyclotomic_order := Sum(weights);
    # Input check:
    if not IsPrimeInt(cyclotomic_order) then
        Error("Sum of m_i must be a prime!");
        return fail;
    fi;
    # To not have to worry about edge cases:
    if (cyclotomic_order mod 12 <> 11) or (cyclotomic_order mod 5 = 1) then
        Error("Sum of m_i does not dodge all the 'generating' edge cases!");
        return fail;
    fi;
    start := NanosecondsSinceEpoch();
    # First precompute a bunch of stuff:
    matrix_of_weight_perms := [];
    for this_permutation in SymmetricGroup(5) do
        Add(matrix_of_weight_perms, Permuted(weights, this_permutation));
    od;
    mod_s_inverses := [1];
    for x in [2..cyclotomic_order-2] do
        y := Gcdex(x, cyclotomic_order).coeff1;
        if y < 0 then
            y := y + cyclotomic_order;
        fi;
        Add(mod_s_inverses, y);
    od;
    p_minus_1 := cyclotomic_order - 1;
    Add(mod_s_inverses, p_minus_1);
    all_e_powers := List([0..cyclotomic_order],x->E(cyclotomic_order) ^ x);
    # ^^^^ We cache all the roots of unity so they don't need to be recalculated every time.

    # This function does the heavy lifting, so we have to copy less code:
    coeffs_cyc_sum := function(base_exponents)
        local e_power, product_so_far, used_powers;

        used_powers := matrix_of_weight_perms * base_exponents;
        used_powers := used_powers mod cyclotomic_order;
        product_so_far := 1;
        for e_power in used_powers do
            product_so_far := product_so_far + product_so_far * all_e_powers[e_power + 1];
        od;
        return Sum(CoeffsCyc(product_so_far, cyclotomic_order));
    end;

    # Now for the actual work, which is split into a bunch of cases after a careful analysis of possibilities:
    final_result := 0;

    # ***** For 3 zeros. Four don't exist, because sum c_i = 0 mod s. *****
    together := [0, 0, 0, 1, p_minus_1];
    final_result := final_result - 10*coeffs_cyc_sum(together);
    #PrintTo(output_file, together, " \'", coeffs_cyc_sum(together), "\n");

    # ***** Next, two zeros possibilities: *****
    together := [0, 0, 1, 1, cyclotomic_order - 2];  # This is there twice (20+10).
    final_result := final_result - 30*coeffs_cyc_sum(together);
    for z in [2..(cyclotomic_order - 3) / 2] do
        last_coordinate := p_minus_1 - z;
        # We want the minimum from:
        # [z,last]
        # [inv_z,last*inv_z] (Sorted)
        # [z*last_inv,last_inv] (Sorted)
        inv_z := mod_s_inverses[z];
        if z > Minimum(inv_z, (last_coordinate * inv_z) mod cyclotomic_order) then
            continue;
        fi;
        inv_last := mod_s_inverses[last_coordinate];
        if z > Minimum(inv_last, (inv_last * z) mod cyclotomic_order) then
            continue;
        fi;
        together := [0, 0, 1, z, last_coordinate];
        final_result := final_result - 60*coeffs_cyc_sum(together);  # Multiplier here is 60, computed before.
    od;
    Print("Done with linear.\n");

    # ***** Then the single zero possibilities: *****
    # Special cases first:
    together := [0, 1, 1, 1, cyclotomic_order - 3];  # This is there twice (15+5).
    final_result := final_result - 20*coeffs_cyc_sum(together);
    together := [0, 1, 1, p_minus_1, p_minus_1];  # This is there once.
    final_result := final_result - 15*coeffs_cyc_sum(together);
    # Then double 1s cases:
    for z in [2..(cyclotomic_order - 3) / 2] do
        together := [0, 1, 1, z, cyclotomic_order - 2 - z];
        final_result := final_result - 60*coeffs_cyc_sum(together);
    od;
    # Then s-1 cases:
    for z in [2..p_minus_1 / 2] do
        last_coordinate := cyclotomic_order - z;
        # We want the minimum from:
        # [z,-z]
        # [inv_z,-inv_z] (Sorted)
        inv_z := mod_s_inverses[z];
        if z > Minimum(inv_z, cyclotomic_order - inv_z) then
            continue;
        fi;
        together := [0, 1, z, last_coordinate, p_minus_1];
        final_result := final_result - 60*coeffs_cyc_sum(together);  # Multiplier here is 60, computed before.
    od;
    # Then "4 distinct entry" cases:
    for z in [3..cyclotomic_order - 2] do
        inv_z := mod_s_inverses[z];
        for y in [2..z - 1] do
            if y > inv_z then
                break;  # No further y's are needed here!
            fi;
            # We want the minimum from:
            # [y,z,last]
            # [y*inv_z,inv_z,last*inv_z] (Sorted)
            # [y_inv,z*y_inv,last*y_inv] (Sorted)
            # [y*last_inv,z*last_inv,last_inv] (Sorted)
            last_coordinate := (- 1 - y - z) mod cyclotomic_order;
            if (z >= last_coordinate) or (last_coordinate = p_minus_1) then
                continue;  # Order isn't preserved here, don't want it.
            fi;
            inv_y := mod_s_inverses[y];
            inv_last := mod_s_inverses[last_coordinate];
            if y > Minimum(inv_y, inv_last) then
                continue;  # More trivial checks for not being the smallest in the orbit.
            fi;
            used_tuple := [1, y, z, last_coordinate];
            is_minimal := true;
            for inverting_element in [inv_y, inv_z, inv_last] do
                new_used_tuple := (used_tuple * inverting_element) mod cyclotomic_order;
                Sort(new_used_tuple);
                if new_used_tuple < used_tuple then
                    is_minimal := false;
                    break;
                fi;
            od;
            if is_minimal then
                together := [0, 1, y, z, last_coordinate];
                final_result := final_result - 120 * coeffs_cyc_sum(together);  # Gotta count 4 distinct 5-tuples.
            fi;
        od;
    od;
    Print("Done with quadratic.\n");

    # ***** Finally, no zero possibilities: *****
    # Special cases first:
    together := [1, 1, 1, 1, cyclotomic_order - 4];  # This is there twice (4+1).
    final_result := final_result - 5*coeffs_cyc_sum(together);
    together := [1, 1, 1, (cyclotomic_order - 3) / 2, (cyclotomic_order - 3) / 2];  # This is there twice (6+4).
    final_result := final_result - 10*coeffs_cyc_sum(together);
    together := [1, 1, 1, cyclotomic_order - 2, cyclotomic_order - 1];  # This is there thrice (12+4+4).
    final_result := final_result - 20*coeffs_cyc_sum(together);
    # Then triple 1s cases:
    for z in [2..(cyclotomic_order - 5) / 2] do
        together := [1, 1, 1, z, cyclotomic_order - 3 - z];
        final_result := final_result - 20*coeffs_cyc_sum(together);  # 12+4+4
    od;
    # Then double 1s cases with another duplicate:
    # Rather single 1 and double duplicate!
    inv_last := mod_s_inverses[2];  # Just to have it easily available.
    for z in [2..p_minus_1] do
        last_coordinate := ((- 1 - z - z) * inv_last) mod cyclotomic_order;
        if (last_coordinate = 1) or (last_coordinate <= z) then
            continue;  # Skip, this was counted already.
        fi;
        together := [1, z, z, last_coordinate, last_coordinate];
        final_result := final_result - 30*coeffs_cyc_sum(together);  # 12+12+6
    od;
    # Then double 1s cases with rest distinct:
    for z in [3..cyclotomic_order - 2] do
        for y in [2..z - 1] do
            last_coordinate := (- 2 - y - z) mod cyclotomic_order;
            if (z < last_coordinate) then
                together := [1, 1, y, z, last_coordinate];
                final_result := final_result - 60 * coeffs_cyc_sum(together);  # 24+12+12+12
            fi;
        od;
    od;

    # Finally, all distinct:

    # We want the minimum from:
    # [x,y,z,last]  <-- We want this to be the minimal one!
    # [inv_x , y*inv_x , z*inv_x , last*inv_x] (Sorted)
    # [x*inv_y , inv_y , z*inv_y , last*inv_y] (Sorted)
    # [x*inv_z , y*inv_z , inv_z , last*inv_z] (Sorted)
    # [x*inv_last , y*inv_last , z*inv_last , inv_last] (Sorted)
    for x in [2..cyclotomic_order - 4] do
        inv_x := mod_s_inverses[x];
        if inv_x < x then
            continue;  # Already not the smallest in the orbit, skip!
        fi;
        Print(x, "\n");
        for y in [x + 1..cyclotomic_order - 3] do
            inv_y := mod_s_inverses[y];
            if inv_y < x then
                continue;  # Already not the smallest in the orbit, skip!
            fi;
            if x > Minimum((y*inv_x) mod cyclotomic_order, (x*inv_y) mod cyclotomic_order) then
                continue;  # Already not the smallest in the orbit, skip!
            fi;
            for z in [y + 1..cyclotomic_order - 2] do
                inv_z := mod_s_inverses[z];
                if inv_z < x then
                    continue;  # Already not the smallest in the orbit, skip!
                fi;
                last_coordinate := (- 1 - x - y - z) mod cyclotomic_order;
                if last_coordinate <= z then
                    continue;  # Skip, not in ascending order.
                fi;
                inv_last := mod_s_inverses[last_coordinate];
                if inv_last < x then
                    continue;  # Already not the smallest in the orbit, skip!
                fi;
                together := [1, x, y, z, last_coordinate];                
                is_minimal := true;
                for inverting_element in [inv_x, inv_y, inv_z, inv_last] do
                    new_used_tuple := (together * inverting_element) mod cyclotomic_order;
                    Sort(new_used_tuple);
                    if new_used_tuple < together then
                        is_minimal := false;
                        break;
                    fi;
                od;
                if is_minimal then
                    final_result := final_result - 120 * coeffs_cyc_sum(together);  # Gotta count 5 distinct 5-tuples.
                fi;
            od;
        od;
    od;

    final_result := (final_result + 2^120) / cyclotomic_order^4;  # The 2^120 is there for the five 0s vector.
    Print("Time taken: ", Int((NanosecondsSinceEpoch() - start) / 1000000), " ms\n");
    return final_result;
end);

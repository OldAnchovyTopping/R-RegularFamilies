# --------------------------------------------------------------------------------------- #
# Note that this version will work on Unix systems only, because it uses the signal.alarm |
# --------------------------------------------------------------------------------------- #

from copy import deepcopy
from itertools import product, permutations, combinations
import signal


# --------------------------------------------------------------------------------------- #
# This chunk creates the matrices obeying the sum condition and scalar product condition. |
# --------------------------------------------------------------------------------------- #


def scalar_product_checking(a: int, b: int, c: int, d: int, e: int, p: int):
    """Returns precisely those vectors that align with the scalar product condition."""
    weight_sum_divisible = [
        [v, w, x, y, z] for v, w, x, y, z in ALL_ROW_VECTORS
        if not (a * v + b * w + c * x + d * y + e * z) % p  # If it's divisible.
    ]
    return weight_sum_divisible


def count_sieve(previous: list[list], permitted: set[int]) -> dict[int, list]:
    """Sieves the list of vectors, letting only those with sum(elements)
    in the set of permitted through. These vectors are also split based on
    their element sum into a dictionary."""
    total_count = 0
    remaining = {size: [] for size in permitted}
    for checked_list in previous:
        its_sum = sum(checked_list)
        if its_sum in permitted:
            remaining[its_sum].append(checked_list)
            total_count += 1
    print(f"There are {total_count} vectors with sum v_i in permitted sizes.")
    return remaining


def matrix_creation(size_split: dict[int, list]) -> dict[int, list]:
    """Creates matrices out of the provided row vectors, such that the matrices
    have all rows and all columns summing up to the same value."""
    total_count = 0
    possible_matrices = {size: [] for size in size_split}
    sum_1, sum_2, sum_3, sum_4, sum_5 = 0, 0, 0, 0, 0
    for size, rows in size_split.items():
        # print(size)
        for i_1, row_1 in enumerate(rows):
            # Increment everything:
            sum_1 += row_1[0]
            sum_2 += row_1[1]
            sum_3 += row_1[2]
            sum_4 += row_1[3]
            sum_5 += row_1[4]
            if (sum_1 > size) or (sum_2 > size) or (sum_3 > size) or \
                    (sum_4 > size) or (sum_5 > size):
                # Overflow, revert and try another one:
                sum_1 -= row_1[0]
                sum_2 -= row_1[1]
                sum_3 -= row_1[2]
                sum_4 -= row_1[3]
                sum_5 -= row_1[4]
                continue
            for i_2, row_2 in enumerate(rows[i_1:], start=i_1):
                # Increment everything:
                sum_1 += row_2[0]
                sum_2 += row_2[1]
                sum_3 += row_2[2]
                sum_4 += row_2[3]
                sum_5 += row_2[4]
                if (sum_1 > size) or (sum_2 > size) or (sum_3 > size) or \
                        (sum_4 > size) or (sum_5 > size):
                    # Overflow, revert and try another one:
                    sum_1 -= row_2[0]
                    sum_2 -= row_2[1]
                    sum_3 -= row_2[2]
                    sum_4 -= row_2[3]
                    sum_5 -= row_2[4]
                    continue
                for i_3, row_3 in enumerate(rows[i_2:], start=i_2):
                    # Increment everything:
                    sum_1 += row_3[0]
                    sum_2 += row_3[1]
                    sum_3 += row_3[2]
                    sum_4 += row_3[3]
                    sum_5 += row_3[4]
                    if (sum_1 > size) or (sum_2 > size) or (sum_3 > size) or \
                            (sum_4 > size) or (sum_5 > size):
                        # Overflow, revert and try another one:
                        sum_1 -= row_3[0]
                        sum_2 -= row_3[1]
                        sum_3 -= row_3[2]
                        sum_4 -= row_3[3]
                        sum_5 -= row_3[4]
                        continue
                    for i_4, row_4 in enumerate(rows[i_3:], start=i_3):
                        # Increment everything:
                        sum_1 += row_4[0]
                        sum_2 += row_4[1]
                        sum_3 += row_4[2]
                        sum_4 += row_4[3]
                        sum_5 += row_4[4]
                        if (sum_1 > size) or (sum_2 > size) or (sum_3 > size) \
                                or (sum_4 > size) or (sum_5 > size):
                            # Overflow, revert and try another one:
                            sum_1 -= row_4[0]
                            sum_2 -= row_4[1]
                            sum_3 -= row_4[2]
                            sum_4 -= row_4[3]
                            sum_5 -= row_4[4]
                            continue
                        for row_5 in rows[i_4:]:
                            # Increment everything:
                            sum_1 += row_5[0]
                            sum_2 += row_5[1]
                            sum_3 += row_5[2]
                            sum_4 += row_5[3]
                            sum_5 += row_5[4]
                            if sum_1 == sum_2 == sum_3 == sum_4 \
                                    == sum_5 == size:
                                total_count += 1
                                # Found a matrix!
                                possible_matrices[size].append(
                                    [row_1[:],
                                     row_2[:],
                                     row_3[:],
                                     row_4[:],
                                     row_5[:]]
                                )
                            # Decrement everything to reset:
                            sum_1 -= row_5[0]
                            sum_2 -= row_5[1]
                            sum_3 -= row_5[2]
                            sum_4 -= row_5[3]
                            sum_5 -= row_5[4]
                        # Decrement everything to reset:
                        sum_1 -= row_4[0]
                        sum_2 -= row_4[1]
                        sum_3 -= row_4[2]
                        sum_4 -= row_4[3]
                        sum_5 -= row_4[4]
                    # Decrement everything to reset:
                    sum_1 -= row_3[0]
                    sum_2 -= row_3[1]
                    sum_3 -= row_3[2]
                    sum_4 -= row_3[3]
                    sum_5 -= row_3[4]
                # Decrement everything to reset:
                sum_1 -= row_2[0]
                sum_2 -= row_2[1]
                sum_3 -= row_2[2]
                sum_4 -= row_2[3]
                sum_5 -= row_2[4]
            # Decrement everything to reset:
            sum_1 -= row_1[0]
            sum_2 -= row_1[1]
            sum_3 -= row_1[2]
            sum_4 -= row_1[3]
            sum_5 -= row_1[4]
    print(f"There are {total_count} matrices with correct column sums.")
    return possible_matrices


def point_overflow_sieve(matrices_split: dict[int, list[tuple[tuple[int]]]]):
    """Witness maker for non-decomposability of matrices, taking into consideration a single point and all other rows and columns."""
    total_count = 0
    remaining_matrices = {size: [] for size in matrices_split}
    for size, matrices in matrices_split.items():
        for matrix in matrices:
            is_achievable = True
            # Check all entries and all lines (columns and rows) for overflow:
            for entry_x, entry_y, line_index in product(range(5), repeat=3):
                target_entry = matrix[entry_y][entry_x]
                if line_index != entry_y:
                    # Not the same row, can check.
                    possible_sum = 0
                    invert_sum = 0
                    for entry_index, new_entry in enumerate(matrix[line_index]):
                        if entry_index == entry_x:
                            continue  # Same column, skip!
                        possible_sum += min(6, new_entry)
                        invert_sum += min(6, 24 - new_entry)
                    # Now check if either overflow happens:
                    if possible_sum < target_entry:
                        is_achievable = False
                        break
                    if invert_sum < 24 - target_entry:
                        is_achievable = False
                        break
                if line_index != entry_x:
                    # Not the same column, can check.
                    possible_sum = 0
                    invert_sum = 0
                    for row_index in range(5):
                        if row_index == entry_y:
                            continue  # Same row, skip!
                        new_entry = matrix[row_index][line_index]
                        possible_sum += min(6, new_entry)
                        invert_sum += min(6, 24 - new_entry)
                    # Now check if either overflow happens:
                    if possible_sum < target_entry:
                        is_achievable = False
                        break
                    if invert_sum < 24 - target_entry:
                        is_achievable = False
                        break
                if not is_achievable:  # Already lost, can move on already.
                    break
            if is_achievable:
                remaining_matrices[size].append(matrix)
                total_count += 1
    print(f"There are {total_count} matrices passing 1-entry check.")
    return remaining_matrices


def general_two_point(matrices_split: dict[int, list[tuple[tuple[int]]]]):
    """Witness maker for non-decomposability of matrices, all possible pairs of points and all other lines not crossing either of the two points."""
    total_count = 0
    remaining_matrices = {size: [] for size in matrices_split}
    for size, matrices in matrices_split.items():
        for matrix in matrices:
            is_achievable = True
            for r_1_i, c_1_i, r_2_i, c_2_i in product(range(5), repeat=4):
                if r_1_i == r_2_i and c_1_i == c_2_i:
                    continue  # Same point, we have already done this before.
                elif c_1_i == c_2_i:
                    # Same column
                    # --> check through other rows without the column:
                    target_sum = matrix[r_1_i][c_1_i] + matrix[r_2_i][c_2_i]
                    for other_index, other_row in enumerate(matrix):
                        if other_index == r_1_i:
                            continue
                        if other_index == r_2_i:
                            continue
                        possible_sum = 0
                        invert_sum = 0
                        for entry_index, new_entry in enumerate(other_row):
                            if entry_index == c_1_i:
                                continue
                            possible_sum += min(12, new_entry)
                            invert_sum += min(12, 24 - new_entry)
                        if possible_sum < target_sum:
                            is_achievable = False
                            break
                        if invert_sum < 48 - target_sum:
                            is_achievable = False
                            break
                    # --> Also check through other columns:
                    for column_index in range(5):
                        if column_index == c_1_i:
                            continue
                        possible_sum = 0
                        invert_sum = 0
                        for row_index in range(5):
                            new_entry = matrix[row_index][column_index]
                            if row_index == r_1_i or row_index == r_2_i:
                                possible_sum += min(6, new_entry)
                                invert_sum += min(6, 24 - new_entry)
                            else:
                                possible_sum += min(12, new_entry)
                                invert_sum += min(12, 24 - new_entry)
                        if possible_sum < target_sum:
                            is_achievable = False
                            break
                        if invert_sum < 48 - target_sum:
                            is_achievable = False
                            break
                elif r_1_i == r_2_i:
                    # Same row
                    # --> check through other columns without the row:
                    target_sum = matrix[r_1_i][c_1_i] + matrix[r_2_i][c_2_i]
                    for column_index in range(5):
                        if column_index == c_1_i:
                            continue
                        if column_index == c_2_i:
                            continue
                        possible_sum = 0
                        invert_sum = 0
                        for row_index in range(5):
                            if row_index == r_1_i:
                                continue
                            new_entry = matrix[row_index][column_index]
                            possible_sum += min(12, new_entry)
                            invert_sum += min(12, 24 - new_entry)
                        if possible_sum < target_sum:
                            is_achievable = False
                            break
                        if invert_sum < 48 - target_sum:
                            is_achievable = False
                            break
                    # --> Also check through other rows:
                    for other_index, other_row in enumerate(matrix):
                        if other_index == r_1_i:
                            continue
                        possible_sum = 0
                        invert_sum = 0
                        for entry_index, new_entry in enumerate(other_row):
                            new_entry = matrix[other_index][entry_index]
                            if entry_index == c_1_i or entry_index == c_2_i:
                                possible_sum += min(6, new_entry)
                                invert_sum += min(6, 24 - new_entry)
                            else:
                                possible_sum += min(12, new_entry)
                                invert_sum += min(12, 24 - new_entry)
                        if possible_sum < target_sum:
                            is_achievable = False
                            break
                        if invert_sum < 48 - target_sum:
                            is_achievable = False
                            break
                else:
                    # Two "independent" entries:
                    target_sum = matrix[r_1_i][c_1_i] + matrix[r_2_i][c_2_i]
                    # Column-wise check:
                    for column_index in range(5):
                        if column_index == c_1_i:
                            continue
                        if column_index == c_2_i:
                            continue
                        possible_sum = 0
                        invert_sum = 0
                        for row_index in range(5):
                            new_entry = matrix[row_index][column_index]
                            inverted_entry = 24 - new_entry
                            if row_index == r_1_i:
                                possible_sum += min(6, new_entry)
                                invert_sum += min(6, inverted_entry)
                            elif row_index == r_2_i:
                                possible_sum += min(6, new_entry)
                                invert_sum += min(6, inverted_entry)
                            else:
                                if new_entry <= 2:
                                    max_contribution = 2 * new_entry
                                else:
                                    max_contribution = new_entry + 2
                                if inverted_entry <= 2:
                                    invert_contribution = 2 * inverted_entry
                                else:
                                    invert_contribution = inverted_entry + 2
                                possible_sum += min(12, max_contribution)
                                invert_sum += min(12, invert_contribution)
                        if possible_sum < target_sum:
                            is_achievable = False
                            break
                        if invert_sum < 48 - target_sum:
                            is_achievable = False
                            break
                if not is_achievable:
                    break
            if is_achievable:
                remaining_matrices[size].append(matrix)
                total_count += 1
    print(f"There are {total_count} matrices passing 2-entry check.")
    return remaining_matrices


def make_sensible_matrices(weights: list[int], prime_modulo: int, wanted_sizes: set[int]):
    """Interface function, performing the above checks in sequence."""
    # Sanity check on inputs:
    assert len(weights) == 5
    p_a, p_b, p_c, p_d, p_e = weights
    assert (p_a + p_b + p_c + p_d + p_e) % prime_modulo == 0
    # assert min(wanted_sizes) >= 0
    # assert max(wanted_sizes) <= 120
    for maybe_div in range(2, int(prime_modulo ** 0.5) + 1):
        if not (prime_modulo % maybe_div):  # It's divisible!
            raise ValueError(f"Input {prime_modulo} is not a prime!")
    available_vectors = \
        scalar_product_checking(p_a, p_b, p_c, p_d, p_e, prime_modulo)
    print(
        f"For w={(p_a, p_b, p_c, p_d, p_e)}, there are {len(available_vectors)} "
        f"row vectors v with v.w = 0 mod {prime_modulo}."
    )
    # Take all wanted sums:
    size_sum_split = count_sieve(available_vectors, wanted_sizes)
    # Having the vectors within the sum-split, make them into matrices:
    made_matrices = matrix_creation(size_sum_split)
    # And toss out the obvious:
    one_point_test_survivors = point_overflow_sieve(made_matrices)
    two_point_test_survivors = general_two_point(one_point_test_survivors)
    return two_point_test_survivors


def scalar_product_check_after_size_split(a: int, b: int, c: int, d: int, e: int, p: int, good_sum_vectors: dict):
    """It might be valuable to do set-size-checking first, this method performs the scalar product condition after size split."""
    total_count = 0
    remaining = {}
    for size, vectors in good_sum_vectors.items():
        remaining[size] = []
        for v, w, x, y, z in vectors:
            if (a * v + b * w + c * x + d * y + e * z) % p:  # If it's NOT divisible.
                continue
            remaining[size].append([v, w, x, y, z])
            total_count += 1
    return remaining, total_count


def make_sensible_matrices_size_split_first(weights: list[int], prime_modulo: int, possible_vectors_in_sum_split: dict[int, list]):
    """Interface function, performing the above checks in sequence, but with swapped scalar product and size check."""
    # Sanity check on inputs:
    assert len(weights) == 5
    p_a, p_b, p_c, p_d, p_e = weights
    assert (p_a + p_b + p_c + p_d + p_e) % prime_modulo == 0
    # assert min(wanted_sizes) >= 0
    # assert max(wanted_sizes) <= 120
    for maybe_div in range(2, int(prime_modulo ** 0.5) + 1):
        if not (prime_modulo % maybe_div):  # It's divisible!
            raise ValueError(f"Input {prime_modulo} is not a prime!")
    available_vectors, count_of_good_vectors = \
        scalar_product_check_after_size_split(p_a, p_b, p_c, p_d, p_e, prime_modulo, possible_vectors_in_sum_split)
    print(
        f"For w={(p_a, p_b, p_c, p_d, p_e)}, there are {count_of_good_vectors} "
        f"row vectors v with v.w = 0 mod {prime_modulo} with permissible sum-size."
    )
    # Having the vectors within the sum-split, make them into matrices:
    made_matrices = matrix_creation(available_vectors)
    # And toss out the obvious:
    one_point_test_survivors = point_overflow_sieve(made_matrices)
    two_point_test_survivors = general_two_point(one_point_test_survivors)
    return two_point_test_survivors


# ------------------------------------------------------------------------------------------------ #
# Next functions are about the brute-force solution to decomposability regarding sets of matrices. |
# ------------------------------------------------------------------------------------------------ #


def brute_recursion(matrix, remaining_perms, position_potentials):
    """If all else fails, it is time to backtrack through all possibilities to verify (non)-decomposability."""
    # Bottom of recursion:
    if matrix.count([0, 0, 0, 0, 0]) == 5:
        return True  # Solution has been found!!
    # print(f"The remaining matrix: {matrix}")
    # print(f"The position potentials: {position_potentials}")
    # Calculate the position with the fewest choices:
    minimum_choices, min_row, min_col = 2704156, 0, 0
    for r_index, c_index in product(range(5), repeat=2):
        actual_entry = matrix[r_index][c_index]
        if not actual_entry:
            continue  # The zero entry is already satisfied!
        entry_potential = position_potentials[r_index][c_index]
        # We are assuming here that we already pruned the branch, if something
        # was overflowing:
        choice_amount = pascal_full[entry_potential][actual_entry]
        # try:
        #     choice_amount = pascal_full[entry_potential][actual_entry]
        # except IndexError:
        #     print(f"The remaining matrix: {matrix}")
        #     print(f"The position potentials: {position_potentials}")
        #     print(entry_potential, actual_entry)
        #     quit()
        if minimum_choices > choice_amount:
            minimum_choices = choice_amount
            min_row = r_index
            min_col = c_index
    matrix_entry = matrix[min_row][min_col]
    # print(f"We shall recurse on the position ({min_row},{min_col}) with "
    #       f"{matrix_entry}/{position_potentials[min_row][min_col]} wanted.")
    # Split the remaining matrices:
    new_remaining = []
    new_potentials = [[0 for _ in range(5)] for _ in range(5)]
    available_here = []
    for perm in remaining_perms:
        if perm[min_row][min_col] == 1:
            available_here.append(perm)
        else:
            new_remaining.append(perm)
            for r_index, c_index in product(range(5), repeat=2):
                new_potentials[r_index][c_index] += perm[r_index][c_index]
    # Now try them and recurse:
    solution_found = False
    for used_matrices in combinations(available_here, matrix_entry):
        the_matrix_after = deepcopy(matrix)
        for perm in used_matrices:
            for r_index, c_index in product(range(5), repeat=2):
                the_matrix_after[r_index][c_index] -= perm[r_index][c_index]
        # Now we need to check that each m_ij has 0 <= m_ij <= potentials_ij:
        should_we_prune = False
        for r_i, c_i in product(range(5), repeat=2):
            if 0 > the_matrix_after[r_i][c_i] or \
                    the_matrix_after[r_i][c_i] > new_potentials[r_i][c_i]:
                should_we_prune = True
                break
        if should_we_prune:
            continue  # Skip to next matrix, this one will not work!
        # If we are here, then we are allowed to recurse:
        solution_found = brute_recursion(
            the_matrix_after, new_remaining, new_potentials
        )
        if not solution_found:
            continue  # Still not done!
        # for perm in used_matrices:
        #     print(perm)
        break
    return solution_found


def timeout_handler(signum, frame):
    """Custom signal handler."""
    raise TimeoutError


signal.signal(signal.SIGALRM, timeout_handler)


def flexible_bruteforce_preparation_with_signal(
    matrices_split: dict[int, list], time_limit: int, strict=False
):
    """Final test for matrices, confirming whether they are splittable or not.
    Calls the recursive brute force after doing some prep work.
    
    One can set different time limits and also decide if strict mode is on."""
    print()
    # First make all the permutation matrices:
    all_perm_mats = [
        [[0 for _ in range(5)] for _ in range(5)] for _ in range(120)
    ]
    for perm_i, permutation in enumerate(permutations(range(5))):
        for mat_index in range(5):
            all_perm_mats[perm_i][mat_index][permutation[mat_index]] = 1
    total_count = 0
    remaining_matrices = {size: [] for size in matrices_split}
    doable_matrices = {size: [] for size in matrices_split}
    only_const_and_impossible = True
    for size, matrices in matrices_split.items():
        for matrix in matrices:
            # listify_matrix = [[0 for _ in range(5)] for _ in range(5)]
            one_value = matrix[0][0]
            the_count = 0
            zero_coordinates = []
            for r_i, c_i in product(range(5), repeat=2):
                if matrix[r_i][c_i] == 0:
                    zero_coordinates.append((r_i, c_i))
                # listify_matrix[r_i][c_i] = matrix[r_i][c_i]
                the_count += matrix[r_i][c_i] == one_value
            if the_count == 25:
                remaining_matrices[size].append(matrix)
                doable_matrices[size].append(matrix)
                print(matrix, "is doable, it's a constant matrix.")
                total_count += 1
                continue  # Constant matrix, we can skip this!
            available_perms = []
            available_potentials = [[0 for _ in range(5)] for _ in range(5)]
            for perm in all_perm_mats:
                for zero_row, zero_col in zero_coordinates:
                    if perm[zero_row][zero_col] == 1:
                        break
                else:
                    # No breaking means no bad positions!
                    available_perms.append(perm)
                    for r_i, c_i in product(range(5), repeat=2):
                        available_potentials[r_i][c_i] += perm[r_i][c_i]
            print(matrix, end=" ")
            should_we_prune = False
            for r_i, c_i in product(range(5), repeat=2):
                if 0 > matrix[r_i][c_i] or \
                        matrix[r_i][c_i] > available_potentials[r_i][c_i]:
                    should_we_prune = True
                    break
            if should_we_prune:
                print("is impossible!")
                continue  # Skip, this matrix got eliminated!
            signal.alarm(time_limit)
            try:
                is_achievable = brute_recursion(
                    deepcopy(matrix), available_perms, available_potentials
                )
                signal.alarm(0)  # Reset the alarm.
            except TimeoutError:
                # results_for_this_set.append(None)
                remaining_matrices[size].append(matrix)
                only_const_and_impossible = False
                print("timed out.")
                signal.alarm(0)  # Reset the alarm.
                continue
            finally:
                signal.alarm(0)  # Reset the alarm, in case some weirdness happened.
            if is_achievable:
                print("is doable.")
                remaining_matrices[size].append(matrix)
                doable_matrices[size].append(matrix)
                only_const_and_impossible = False
                total_count += 1
                if strict:
                    print("Because of enabled strict mode, the function was terminated.")
                    return remaining_matrices, doable_matrices, None
            else:
                print("is impossible!")
    print(f"There are {total_count} matrices passing brute-force check.")
    return remaining_matrices, doable_matrices, only_const_and_impossible


def print_matrices(catalogued_matrices):
    """Utility function for printing the remaining matrices at a desired moment."""
    print_mode = input("Do you want counts for all sizes (c), all matrices (m), or nothing (n)? ")
    if print_mode == "c":
        for size, list_of_matrices in catalogued_matrices.items():
            print(size, len(list_of_matrices))
    elif print_mode == "m":
        for size, list_of_matrices in catalogued_matrices.items():
            for matrix in list_of_matrices:
                print(matrix)
    elif print_mode == "n":
        print()
    else:
        print(f"The mode {print_mode} is not supported. Continuing in the program...")


# ------------------------------------------------------------------------------------ #
# Finally we have both the interactive app and the multisieving file reading function. |
# ------------------------------------------------------------------------------------ #


def console_app_main():
    """Main function of the console app. The app prompts the user for input weights and set sizes, then computes."""
    # First we sieve out the row vectors:
    print("You will need to input the 5 weights and prime modulus.")
    while True:
        weight_prompt = "Enter 5 weights: "
        p_a, p_b, p_c, p_d, p_e = (int(k) for k in input(weight_prompt).split())
        prime_divisor_prompt = "Enter the prime dividing the weight sum: "
        prime_modulo = int(input(prime_divisor_prompt))
        for maybe_div in range(2, int(prime_modulo ** 0.5) + 1):
            if not (prime_modulo % maybe_div):  # It's divisible!
                print(f"{prime_modulo} is not a prime.")
                break
        else:  # Only accessed if no loop break happened.
            # Check the dividing property:
            quotient, remainder = divmod(p_a + p_b + p_c + p_d + p_e, prime_modulo)
            if remainder != 0:
                print("Try again!")
            else:
                break
    print(f"The sum of inputs in this case is {p_a + p_b + p_c + p_d + p_e} = "
          f"{quotient} * {prime_modulo}.")
    # Then we take those with good element sum:
    size_prompt = \
        "Enter all acceptable subset sizes separated by spaces.\nIf you want " \
        "to have all numbers between 0-120 that are divisible by k, type -k: "
    used_sum_set = {int(k) for k in input(size_prompt).split()}
    if len(used_sum_set) == 1:
        the_element = used_sum_set.pop()
        if the_element < 0:
            used_sum_set = set(range(0, 121, -the_element))
        else:
            used_sum_set = {the_element}
    leftover_matrices = make_sensible_matrices(
        [p_a, p_b, p_c, p_d, p_e], prime_modulo, used_sum_set
    )
    print_matrices(leftover_matrices)
    want_strict_mode = \
        input("Do you want the brute force to terminate after finding a "
              "non-constant splittable matrix? (y/n): ")
    strictness = want_strict_mode == "y"
    leftover_matrices, confirmed_doable_matrices, only_constant_doable = \
        flexible_bruteforce_preparation_with_signal(leftover_matrices, 0, strictness)
    print_matrices(leftover_matrices)


def multi_sieve_file():
    """Accepts a file of many inputs in the form [weight_sum, [w_1, w_2, w_3, w_4, w_5]] and performs multiple sieving protocols with different cutoff times."""
    print("The current protocol is: \n - a strict 2-second test \n - a strict 10-second test \n - a strict 1-minute test \n - a strict unbounded test")
    with open(THE_FILE_NAME, 'r') as input_file:
        file_data = input_file.read().strip().replace('\n', '')
    first_split = file_data.split(";")
    stringed_sum_list = first_split[0].split(":=")[1]
    if ".." in stringed_sum_list:
        bounds = stringed_sum_list.split("..")
        lower = int(bounds[0].strip()[1:])
        upper = int(bounds[1].strip()[:-1])
        used_sum_set = set(range(lower, upper + 1))
    else:
        used_sum_set = set(s for s in eval(stringed_sum_list))
    # Take all wanted sums:
    permitted_sum_vectors = {size: [] for size in used_sum_set}
    for checked_tuple in ALL_ROW_VECTORS:
        its_sum = sum(checked_tuple)
        if its_sum in permitted_sum_vectors:
            permitted_sum_vectors[its_sum].append(checked_tuple)
    wanted_count = tuple(map(lambda x: x % 5, used_sum_set)).count(0)
    all_parameters_to_test = eval(first_split[1].split(":=")[1])
    all_doable_matrices = []
    for prime_modulo, (p_a, p_b, p_c, p_d, p_e) in all_parameters_to_test:
        print(f"\n{'/' * 150}\n")
        leftover_matrices = make_sensible_matrices_size_split_first(
            [p_a, p_b, p_c, p_d, p_e], prime_modulo, permitted_sum_vectors
        )
        # print_matrices(leftover_matrices)
        for allowed_time_limit, next_limit in zip((2, 10, 60, 0), ("with 10 second", "with 60 second", "WITHOUT", "!!!NOTHING, this should not show up during program run!!!")):
            leftover_matrices, confirmed_doable_matrices, are_we_done = \
                flexible_bruteforce_preparation_with_signal(leftover_matrices, allowed_time_limit, True)
            all_doable_matrices.append(confirmed_doable_matrices)
            if are_we_done is None:
                break  # Strict mode shut us down!
            if are_we_done:  # True, so we halt.
                print_matrices(leftover_matrices)
                break
            elif sum(map(lambda x: len(x), confirmed_doable_matrices.values())) != wanted_count:
                break  # Not a set that has potential!
            print(f"\n{'*' * 150}\nRedoing {next_limit} time limit.\n{'*' * 150}")
    print(f"\n{'/' * 150}\n")
    # Write down the decomposable matrices into a file:
    file_ending = "-".join(c for c in THE_FILE_NAME.split("_")[1:])
    with open(f"rozlozitelne_{file_ending}", "w") as output_file:
        for dict_of_splittable_matrices in all_doable_matrices:
            for splittable_matrices in dict_of_splittable_matrices.values():
                output_file.write(f"Append(rozlozitelne,{splittable_matrices});\n")


if __name__ == '__main__':
    ALL_ROW_VECTORS = tuple(product(range(25), repeat=5))
    # Initialise the Pascal Triangle for "optimal" choices:
    pascal_full: list[list[int]] = [[1]]
    for pascal_row_index in range(1, 25):
        new_row = [1]
        for x in range(1, pascal_row_index):
            new_row.append(pascal_full[-1][x - 1] + pascal_full[-1][x])
        new_row.append(1)
        pascal_full.append(new_row)
    # Now run the program:
    COMMANDS = {
        "a": console_app_main,
        # "f": process_file_through_one_test,
        "s": multi_sieve_file
    }
    interaction_prompt = \
        "Do you want to open the console app (a) or multi-test-sieve a file (s)? "
        # "Do you want to open the console app (a), check through a file (f), or multi-test-sieve (s)? "
    interaction_mode = ""
    while interaction_mode not in COMMANDS:
        interaction_mode = input(interaction_prompt)
    if interaction_mode != "a":
        # Here we read from a file.
        THE_FILE_NAME = input("Type out the file name: ")
    COMMANDS[interaction_mode]()  # Execute the appropriate "protocol".

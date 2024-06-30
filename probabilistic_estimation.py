from copy import deepcopy
from itertools import combinations, permutations
from random import randint


class RegularFamilies:
    def __init__(self, regularity: int, filtering: list[int]):
        self.n = ELEMENT_COUNT
        self.r = regularity
        # Now partition the permutations into the S_i sets. 
        self.first_elem_split = [[] for _ in range(self.n)]
        for perm in permutations(range(self.n)):
            self.first_elem_split[perm[0]].append(perm)
        # More setup variables:
        self.there_are_this_many_of_us = 0
        self.there_are_roughly_this_many_of_us = 0
        self.filtering_probabilities = filtering
        self.depths_let_forward = [0 for _ in range(self.n)]
        self.depths_reached = [0 for _ in range(self.n)]

    def check_if_can_be_regular(self, partial_family):
        """Helper method to check overflows for every number and position."""
        assigned_counts = [[0 for _ in range(self.n)] for _ in range(self.n)]
        for perm in partial_family:
            for index in range(self.n):
                assigned_counts[index][perm[index]] += 1
                if assigned_counts[index][perm[index]] > self.r:
                    # This position overflowed on this number.
                    return False
        return True

    def generate_all(self, partial_family: list, depth: int = 0):
        """Generating all the families and yielding them one by one."""
        if depth == self.n:
            if self.check_if_can_be_regular(partial_family):
                yield partial_family
        else:
            for chosen_ps in combinations(self.first_elem_split[depth], self.r):
                new_partial = partial_family[:]
                new_partial.extend(chosen_ps)
                if not self.check_if_can_be_regular(new_partial):
                    continue
                yield from self.generate_all(new_partial, depth + 1)

    def count_all(self, partial_counts: list, depth: int = 0):
        """Counting all the families, takes VERY long for n>4."""
        if depth == self.n:
            for row in partial_counts:
                broken = False
                for entry in row:
                    if entry > self.r:
                        broken = True
                        break
                if broken:
                    break
            else:
                self.there_are_this_many_of_us += 1
        else:
            for chosen_ps in combinations(self.first_elem_split[depth], self.r):
                new_partial = deepcopy(partial_counts)
                for perm in chosen_ps:
                    broken = False
                    for index, value in enumerate(perm):
                        new_partial[index][value] += 1
                        if new_partial[index][value] > self.r:
                            broken = True
                            break
                    if broken:
                        break
                else:
                    self.count_all(new_partial, depth + 1)

    def probability_recursion(self, partial_counts: list, depth: int = 0):
        """The main function for our estimation heuristic."""
        if depth == self.n:  # No checking needed!
            self.there_are_roughly_this_many_of_us += 1
        else:
            for chosen_ps in combinations(self.first_elem_split[depth], self.r):
                new_partial = deepcopy(partial_counts)
                for perm in chosen_ps:
                    broken = False
                    for index, value in enumerate(perm):
                        new_partial[index][value] += 1
                        if new_partial[index][value] > self.r:
                            # This position with this number has overflown.
                            broken = True
                            break
                    if broken:
                        break
                else:  # Utilising the odd for...else... Python quirk.
                    self.depths_reached[depth] += 1
                    if randint(1, self.filtering_probabilities[depth]) == 1:
                        self.depths_let_forward[depth] += 1
                    else:
                        continue
                    # The recursive call executes with 1/p probability
                    self.probability_recursion(new_partial, depth + 1)

    def count_probabilistically(self):
        """Interface function for the randomised recursion."""
        new_zeros = deepcopy(ZERO_ED_COUNTER)  # Setup.
        self.probability_recursion(new_zeros, 0)  # Recursion call.
        # After that's done, multiply and divide based on the obtained numbers:
        for forward, total in zip(self.depths_let_forward, self.depths_reached):
            if forward == 0:
                raise ValueError(f"{self.depths_let_forward} / "
                                 f"{self.depths_reached}")
            self.there_are_roughly_this_many_of_us *= total
            self.there_are_roughly_this_many_of_us /= forward
        return round(self.there_are_roughly_this_many_of_us)


if __name__ == '__main__':
    # ELEMENT_COUNT = 4
    # regular_table_counts = [1]
    # all_probability_filters = [
    #     # r = 0 is trivial
    #     [2, 1, 2, 1],
    #     [1, 10, 1, 1],
    #     [2, 5, 1, 1],
    # ]
    # Above is the n=4 case.
    ELEMENT_COUNT = 5
    regular_table_counts = [1, 1344]
    all_probability_filters = [
        # r = 0 is trivial
        # r = 1 is known
        [10, 30, 30, 15, 1],
        [100, 200, 200, 60, 1],
        [350, 2000, 3000, 200, 1],
        [900, 16000, 24000, 600, 1],
        [1900, 80000, 47000, 1000, 1],
        [4500, 390000, 97000, 1500, 1],
        [9300, 1900000, 200000, 2100, 1],
        [22000, 4000000, 400000, 4000, 1],
        [33000, 4900000, 800000, 6700, 1],
        [41000, 6000000, 1560000, 8900, 1],
        [45000, 6500000, 2800000, 10000, 1]
    ]
    ZERO_ED_COUNTER = [
        [0 for _ in range(ELEMENT_COUNT)] for _ in range(ELEMENT_COUNT)
    ]
    repeat_count = 1
    for reg_index, filters in enumerate(all_probability_filters, start=2):
        print(reg_index)
        trial_sum = 0
        for _ in range(repeat_count):
            family = RegularFamilies(reg_index, filters)
            partial = family.count_probabilistically()
            trial_sum += partial
            print(partial, family.depths_let_forward, family.depths_reached)
        result = trial_sum // repeat_count  # Just round down.
        print(result)
        regular_table_counts.append(result)
    print()
    print(regular_table_counts)
    # Last one should be counted only once, not twice!
    print(2 * sum(regular_table_counts) - regular_table_counts[-1])

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <windows.h>
// ------------------------------------------------------------------------------------------
// THESE ARE OUR INPUTS:
#define a 1
#define b 3
#define c 409
#define d 803
#define e 1123
#define order_of_cyclotomics (a+b+c+d+e)
//#define order_of_cyclotomics 2819
#define WORKER_COUNT 12
#define perm_count 120
#define y_power_count 31
#define max_phase (y_power_count - 1)
// ------------------------------------------------------------------------------------------
struct cyclotomic_counters {
    // The array has 121 rows, each for different power of the "counting" variable.
    // Then each row is a prime-order cyclotomic basis, except we have the rational coordinate too:
    __uint128_t coefficients[y_power_count][order_of_cyclotomics];
};
struct cyclotomic_counters multiplyBy(struct cyclotomic_counters the_cyclo_counter, int power, int phase) {
    // Multiplying the previous cyclotomic_counters by a (1+y*\zeta^power).
    if (phase >= y_power_count) {
        phase = max_phase;
    }
    for (int phase_index = phase; phase_index > 1; phase_index--) {
        int previous_phase_index = phase_index - 1;
        for (int i = 0; i < order_of_cyclotomics - power; i++) { // First chunk of coefficient shifting
            the_cyclo_counter.coefficients[phase_index][power + i] += (__uint128_t) the_cyclo_counter.coefficients[previous_phase_index][i];
            //printf("%d ", power + i);
        }
        //printf("\n");
        for (int i = 0; i < power; i++) {
            the_cyclo_counter.coefficients[phase_index][i] += (__uint128_t) the_cyclo_counter.coefficients[previous_phase_index][order_of_cyclotomics - power + i];
            //printf("%d ", i);
        }
        //printf("\n");
    }
    the_cyclo_counter.coefficients[1][power] += 1;  // The trivial operation.
    return the_cyclo_counter;
}
// Global variables:

// We are starting with the number 1 as a cyclotomic_counters number repeatedly, so we will copy it from an existing source.
struct cyclotomic_counters cyc_rational_one;
// Prepare the matrix of all 5! permutation weights that will be used for computation.
int matrix_of_weight_perms[perm_count][5] = {
    {a, b, c, d, e},
    {a, b, c, e, d},
    {a, b, d, c, e},
    {a, b, d, e, c},
    {a, b, e, c, d},
    {a, b, e, d, c},
    {a, c, b, d, e},
    {a, c, b, e, d},
    {a, c, d, b, e},
    {a, c, d, e, b},
    {a, c, e, b, d},
    {a, c, e, d, b},
    {a, d, b, c, e},
    {a, d, b, e, c},
    {a, d, c, b, e},
    {a, d, c, e, b},
    {a, d, e, b, c},
    {a, d, e, c, b},
    {a, e, b, c, d},
    {a, e, b, d, c},
    {a, e, c, b, d},
    {a, e, c, d, b},
    {a, e, d, b, c},
    {a, e, d, c, b},
    {b, a, c, d, e},
    {b, a, c, e, d},
    {b, a, d, c, e},
    {b, a, d, e, c},
    {b, a, e, c, d},
    {b, a, e, d, c},
    {b, c, a, d, e},
    {b, c, a, e, d},
    {b, c, d, a, e},
    {b, c, d, e, a},
    {b, c, e, a, d},
    {b, c, e, d, a},
    {b, d, a, c, e},
    {b, d, a, e, c},
    {b, d, c, a, e},
    {b, d, c, e, a},
    {b, d, e, a, c},
    {b, d, e, c, a},
    {b, e, a, c, d},
    {b, e, a, d, c},
    {b, e, c, a, d},
    {b, e, c, d, a},
    {b, e, d, a, c},
    {b, e, d, c, a},
    {c, a, b, d, e},
    {c, a, b, e, d},
    {c, a, d, b, e},
    {c, a, d, e, b},
    {c, a, e, b, d},
    {c, a, e, d, b},
    {c, b, a, d, e},
    {c, b, a, e, d},
    {c, b, d, a, e},
    {c, b, d, e, a},
    {c, b, e, a, d},
    {c, b, e, d, a},
    {c, d, a, b, e},
    {c, d, a, e, b},
    {c, d, b, a, e},
    {c, d, b, e, a},
    {c, d, e, a, b},
    {c, d, e, b, a},
    {c, e, a, b, d},
    {c, e, a, d, b},
    {c, e, b, a, d},
    {c, e, b, d, a},
    {c, e, d, a, b},
    {c, e, d, b, a},
    {d, a, b, c, e},
    {d, a, b, e, c},
    {d, a, c, b, e},
    {d, a, c, e, b},
    {d, a, e, b, c},
    {d, a, e, c, b},
    {d, b, a, c, e},
    {d, b, a, e, c},
    {d, b, c, a, e},
    {d, b, c, e, a},
    {d, b, e, a, c},
    {d, b, e, c, a},
    {d, c, a, b, e},
    {d, c, a, e, b},
    {d, c, b, a, e},
    {d, c, b, e, a},
    {d, c, e, a, b},
    {d, c, e, b, a},
    {d, e, a, b, c},
    {d, e, a, c, b},
    {d, e, b, a, c},
    {d, e, b, c, a},
    {d, e, c, a, b},
    {d, e, c, b, a},
    {e, a, b, c, d},
    {e, a, b, d, c},
    {e, a, c, b, d},
    {e, a, c, d, b},
    {e, a, d, b, c},
    {e, a, d, c, b},
    {e, b, a, c, d},
    {e, b, a, d, c},
    {e, b, c, a, d},
    {e, b, c, d, a},
    {e, b, d, a, c},
    {e, b, d, c, a},
    {e, c, a, b, d},
    {e, c, a, d, b},
    {e, c, b, a, d},
    {e, c, b, d, a},
    {e, c, d, a, b},
    {e, c, d, b, a},
    {e, d, a, b, c},
    {e, d, a, c, b},
    {e, d, b, a, c},
    {e, d, b, c, a},
    {e, d, c, a, b},
    {e, d, c, b, a}
};
// To calculate inverses only once, pre-calculated at the start:
int inverses[order_of_cyclotomics];
// For the five input "base exponents" of the function:
int base_exponents[5];
// Finally declare the aggregate variable that will store the result:
__uint128_t final_result[y_power_count];
// __uint128_t sum_bound;
HANDLE accum_mutex;
int last_not_done_task;
int thread_task_limit;
HANDLE task_mutex;
SYNCHRONIZATION_BARRIER barrier;

int extendedGCD(int x, int y, int* inv_x, int* inv_y)
// Adapted from https://www.geeksforgeeks.org/c-program-for-basic-and-extended-euclidean-algorithms-2/
{
    // Base Case
    if (x == 0) {
        *inv_x = 0;
        *inv_y = 1;
        return y;
    }

    int x1, y1; // To store results of recursive call
    int gcd = extendedGCD(y % x, x, &x1, &y1);

    // Update the inverses using results of recursive call
    *inv_x = y1 - (y / x) * x1;
    *inv_y = x1;

    return gcd;
}

void swap(int *x,int *y) {
   int temp = *x;
   *x = *y;
   *y = temp;
}

static inline void setCoordinates(
    int coordinates[static 5], int c0, int c1, int c2, int c3, int c4
) {
    coordinates[0] = c0;
    coordinates[1] = c1;
    coordinates[2] = c2;
    coordinates[3] = c3;
    coordinates[4] = c4;
}

static inline void addToFinalResultWithMultiplier(
    __uint128_t increments[static y_power_count], int multiplier
) {
    for (int index = 0; index < y_power_count; index++) {
        final_result[index] += multiplier * increments[index];
        // sum_bound += multiplier * increments[index];
    }
}

static inline void computeProductValue(int baseExponents[static 5], __uint128_t *output) {
    struct cyclotomic_counters cyc_product = cyc_rational_one;
    int power_index, auxiliary_index;
    int power_in_bracket;
    for (power_index = 0; power_index < perm_count; power_index++) {
        //printf("%d ", power_index);
        power_in_bracket = 0;
        for (auxiliary_index = 0; auxiliary_index < 5; auxiliary_index++) {
            //printf("%d*%d ", baseExponents[auxiliary_index], matrix_of_weight_perms[power_index][auxiliary_index]);
            power_in_bracket += baseExponents[auxiliary_index] * matrix_of_weight_perms[power_index][auxiliary_index];
        }
        power_in_bracket = power_in_bracket % order_of_cyclotomics;
        //printf("%d\n", power_in_bracket);
        cyc_product = multiplyBy(cyc_product, power_in_bracket, power_index + 1);
    }
    for (power_index = 0; power_index < y_power_count; power_index++) {
        output[power_index] = cyc_product.coefficients[power_index][0] * (order_of_cyclotomics - 1);
        for (auxiliary_index = 1; auxiliary_index < order_of_cyclotomics; auxiliary_index++) {
            output[power_index] -= cyc_product.coefficients[power_index][auxiliary_index];
        }
    }
}

static inline void computeProductValueWithoutReset(int baseExponents[static 5], __uint128_t *output) {
    struct cyclotomic_counters cyc_product = cyc_rational_one;
    int power_index, auxiliary_index;
    int power_in_bracket;
    for (power_index = 0; power_index < perm_count; power_index++) {
        //printf("%d ", power_index);
        power_in_bracket = 0;
        for (auxiliary_index = 0; auxiliary_index < 5; auxiliary_index++) {
            //printf("%d*%d ", baseExponents[auxiliary_index], matrix_of_weight_perms[power_index][auxiliary_index]);
            power_in_bracket += baseExponents[auxiliary_index] * matrix_of_weight_perms[power_index][auxiliary_index];
        }
        power_in_bracket = power_in_bracket % order_of_cyclotomics;
        //printf("%d\n", power_in_bracket);
        cyc_product = multiplyBy(cyc_product, power_in_bracket, power_index + 1);
    }
    for (power_index = 0; power_index < y_power_count; power_index++) {
        output[power_index] += cyc_product.coefficients[power_index][0] * (order_of_cyclotomics - 1);
        for (auxiliary_index = 1; auxiliary_index < order_of_cyclotomics; auxiliary_index++) {
            output[power_index] -= cyc_product.coefficients[power_index][auxiliary_index];
        }
    }
}

void processXEqualTo(int x) {
    // Variables used:
    int i, y, z, last, inv_x, inv_y, inv_z, inv_last, new_one, new_x, new_y, new_z, new_last;
    int is_minimal;
    int long_multipliers[4];
    int five_different_base_exponents[5];
    __uint128_t partial_result_for_this_x[y_power_count];
    for (int power_index = 0; power_index < y_power_count; power_index++) {
        partial_result_for_this_x[power_index] = (__uint128_t) 0;
    }

    // We want the minimum from:
    // [x,y,z,last]  <-- We want this to be the minimal one!
    // [inv_x , y*inv_x , z*inv_x , last*inv_x] (Sorted)
    // [x*inv_y , inv_y , z*inv_y , last*inv_y] (Sorted)
    // [x*inv_z , y*inv_z , inv_z , last*inv_z] (Sorted)
    // [x*inv_last , y*inv_last , z*inv_last , inv_last] (Sorted)
    inv_x = inverses[x];
    if (inv_x < x) {
        printf("Task x=%d skipped (%d < %d).\n", x, inv_x, x);
        return;  // Already not the smallest in the orbit, skip completely!
    }
    for (y = x+1; y <= order_of_cyclotomics - 3; y++) {
        inv_y = inverses[y];
        if (inv_y < x) {
            continue;  // Already not the smallest in the orbit, skip!
        }
        if ((x > (y*inv_x) % order_of_cyclotomics) || (x > (x*inv_y) % order_of_cyclotomics)) {
            continue;  // Already not the smallest in the orbit, skip!
        }
        for (z = y+1; z <= order_of_cyclotomics - 2; z++) {
            inv_z = inverses[z];
            if (inv_z < x) {
                continue;  // Already not the smallest in the orbit, skip!
            }
            last = (3 * order_of_cyclotomics - 1 - x - y - z) % order_of_cyclotomics;
            if (last <= z) {
                continue;  // Skip, not in ascending order.
            }
            inv_last = inverses[last];
            if (inv_last < x) {
                continue;  // Already not the smallest in the orbit, skip!
            }
            long_multipliers[0] = inv_x;
            long_multipliers[1] = inv_y;
            long_multipliers[2] = inv_z;
            long_multipliers[3] = inv_last;
            is_minimal = 1;
            for (i = 0; i < 4; i++) {
                // Get new values:
                new_one = (long_multipliers[i] * 1) % order_of_cyclotomics;
                new_x = (long_multipliers[i] * x) % order_of_cyclotomics;
                new_y = (long_multipliers[i] * y) % order_of_cyclotomics;
                new_z = (long_multipliers[i] * z) % order_of_cyclotomics;
                new_last = (long_multipliers[i] * last) % order_of_cyclotomics;
                // Now sort the five new values:
                // Needed swaps: [1 2][3 4][1 3][2 5][1 2][3 4][2 3][4 5][3 4] (from https://stackoverflow.com/a/3903172)
                if(new_one>new_x) swap(&new_one,&new_x);
                if(new_y>new_z) swap(&new_y,&new_z);
                if(new_one>new_y) swap(&new_one,&new_y);
                if(new_x>new_last) swap(&new_x,&new_last);
                if(new_one>new_x) swap(&new_one,&new_x);
                if(new_y>new_z) swap(&new_y,&new_z);
                if(new_x>new_y) swap(&new_x,&new_y);
                if(new_z>new_last) swap(&new_z,&new_last);
                if(new_y>new_z) swap(&new_y,&new_z);
                //printf("%d %d %d %d %d\n", new_one, new_x, new_y, new_z, new_last);
                // And finally compare this to the previous:
                if (new_one != 1) {
                    printf("Something went horribly wrong!");
                    return ;
                }
                if (new_x < x) {
                    //printf("%d %d %d %d > %d %d %d %d\n", 1, y, z, last, new_one, new_y, new_z, new_last);
                    is_minimal = 0;
                    break;
                } else {
                    if ((new_x == x) && (new_y < y)) {
                        //printf("%d %d %d %d > %d %d %d %d\n", 1, y, z, last, new_one, new_y, new_z, new_last);
                        is_minimal = 0;
                        break;
                    } else {
                        if ((new_x == x) && (new_y == y) && (new_z < z)) {
                            //printf("%d %d %d %d > %d %d %d %d\n", 1, y, z, last, new_one, new_y, new_z, new_last);
                            is_minimal = 0;
                            break;
                        } else {
                            if ((new_x == x) && (new_y == y) && (new_z == z) && (new_last < last)) {
                                //printf("%d %d %d %d > %d %d %d %d\n", 1, y, z, last, new_one, new_y, new_z, new_last);
                                is_minimal = 0;
                                break;
                            }
                        }
                    }
                }
            }
            if (is_minimal == 1) {
                setCoordinates(five_different_base_exponents, 1, x, y, z, last);
                // So that we use the mutex only once!
                computeProductValueWithoutReset(five_different_base_exponents, partial_result_for_this_x);
            }
        }
    }
    WaitForSingleObject(accum_mutex, INFINITE);
    addToFinalResultWithMultiplier(partial_result_for_this_x, 120);
    // printf("Task x=%d finished:\t\t%016llx%016llx\n", x, (uint64_t)(sum_bound>>64),(uint64_t)sum_bound);
    ReleaseMutex(accum_mutex);
    printf("Task x=%d finished.\n", x);
    return;
}

void taskPicker() {
    int next_task_x;
    while (1) {
        WaitForSingleObject(task_mutex, INFINITE);
        if (last_not_done_task == thread_task_limit) {
            ReleaseMutex(task_mutex);
            break;
        }
        next_task_x = last_not_done_task;
        last_not_done_task++;
        ReleaseMutex(task_mutex);
        processXEqualTo(next_task_x);
        //printf("Task x=%d finished concurrently.\n",next_task_x);
    }
    EnterSynchronizationBarrier(&barrier, SYNCHRONIZATION_BARRIER_FLAGS_BLOCK_ONLY);
}

int main()
{
    clock_t tic = clock();
    // First comes preparation work.
    // Edge case checking:
    /*
    if ((order_of_cyclotomics % (int) 12 != 11) || (order_of_cyclotomics % 5 == 1)) {
        printf("Edge case not avoided!\n%d =/= 11 (mod 12)\nOR\n%d = 1 (mod 5).\n", order_of_cyclotomics, order_of_cyclotomics);
        return 1;
    }*/
    printf("!!Primality is not tested!!\n%d\n", order_of_cyclotomics);
    // Create the "1" of cyclotomic_counters:
    int i, j;
    for (j = 0; j < y_power_count; j++) {
        for (i = 0; i < order_of_cyclotomics; i++) {
            cyc_rational_one.coefficients[j][i] = 0;
        }
    }
    cyc_rational_one.coefficients[0][0] = 1;

    // Pre-compute all the inverses, first the easy cases:
    inverses[0] = 0;
    inverses[1] = 1;
    inverses[order_of_cyclotomics - 1] = order_of_cyclotomics - 1;
    int x, y, z, last; // These will be needed later.
    int inv_x, inv_y, inv_z, inv_last; // These four will be handy.
    for (i = 2; i < order_of_cyclotomics; i++) {
        extendedGCD(order_of_cyclotomics, i, &inv_x, &inv_y);
        if (inv_y < 0) {
            inv_y += order_of_cyclotomics;
        }
        inverses[i] = inv_y;
        //printf("%d, %d\n", i, inv_y);
    }
    int sum_minus_1 = order_of_cyclotomics - 1; // Makes a couple of parts cleaner.

    // Now comes the meat of the required work:
    __uint128_t y_coef_output[y_power_count] = {};
    //sum_bound = 1;
    // ***** For 5 zeros. *****
    final_result[0] = 1;
    __uint128_t binomial = 1;
    for (i = 1; i < y_power_count; i++) {
        binomial = (__uint128_t) (binomial * (121 - i)) / i;
        final_result[i] = binomial;
        //sum_bound += binomial;
    }
    //printf("Hex after 5 zeros:\t\t%016llx%016llx \n",(uint64_t)(sum_bound>>64),(uint64_t)sum_bound);
    printf("Done 5 zeros.\n");
    // ***** For 3 zeros. Four don't exist, because sum c_i = 0 mod s. *****
    setCoordinates(base_exponents, 0, 0, 0, 1, sum_minus_1);
    computeProductValue(base_exponents, y_coef_output);
    addToFinalResultWithMultiplier(y_coef_output, 10);
    //printf("Hex after 5 and 3 zeros:\t%016llx%016llx \n",(uint64_t)(sum_bound>>64),(uint64_t)sum_bound);
    printf("Done 3 zeros.\n");

    // ***** Next, two zeros possibilities: *****
    setCoordinates(base_exponents, 0, 0, 1, 1, order_of_cyclotomics - 2); // This is there twice (20+10).
    computeProductValue(base_exponents, y_coef_output);
    addToFinalResultWithMultiplier(y_coef_output, 30);
    for (z = 2; z <= (order_of_cyclotomics - 3) / 2; z++) {
        last = sum_minus_1 - z;
        // We want the minimum from:
        // [z,last]
        // [inv_z,last*inv_z] (Sorted)
        // [z*last_inv,last_inv] (Sorted)
        inv_z = inverses[z];
        if ((z > inv_z) || (z > (last * inv_z) % order_of_cyclotomics)) {
            continue;
        }
        inv_last = inverses[last];
        if ((z > inv_last) || (z > (inv_last * z) % order_of_cyclotomics)) {
            continue;
        }
        setCoordinates(base_exponents, 0, 0, 1, z, last);
        computeProductValue(base_exponents, y_coef_output);
        addToFinalResultWithMultiplier(y_coef_output, 60);  // Multiplier here is 60, computed before.
    }
    //printf("Hex after 2 zeros:\t\t%016llx%016llx \n",(uint64_t)(sum_bound>>64),(uint64_t)sum_bound);
    printf("Done 2 zeros.\n");

    // ***** Then the single zero possibilities: *****
    // Special cases first:
    setCoordinates(base_exponents, 0, 1, 1, 1, order_of_cyclotomics - 3); // This is there twice (15+5).
    computeProductValue(base_exponents, y_coef_output);
    addToFinalResultWithMultiplier(y_coef_output, 20);
    setCoordinates(base_exponents, 0, 1, 1, order_of_cyclotomics - 1, order_of_cyclotomics - 1); // This is there once.
    computeProductValue(base_exponents, y_coef_output);
    addToFinalResultWithMultiplier(y_coef_output, 15);
    // Then double 1s cases:
    for (z = 2; z <= (order_of_cyclotomics - 3) / 2; z++) {
        setCoordinates(base_exponents, 0, 1, 1, z, order_of_cyclotomics - 2 - z);
        computeProductValue(base_exponents, y_coef_output);
        addToFinalResultWithMultiplier(y_coef_output, 60);
    }
    // Then s-1 cases:
    for (z = 2; z <= sum_minus_1 / 2; z++) {
        last = order_of_cyclotomics - z;
        // We want the minimum from:
        // [z,-z]
        // [inv_z,-inv_z] (Sorted)
        inv_z = inverses[z];
        if ((z > inv_z) || (z > order_of_cyclotomics - inv_z)) {
            continue;
        }
        setCoordinates(base_exponents, 0, 1, z, last, sum_minus_1); // Multiplier here is 60, computed before.
        computeProductValue(base_exponents, y_coef_output);
        addToFinalResultWithMultiplier(y_coef_output, 60);
    }
    //printf("Hex result: %016llx%016llx \n",(uint64_t)(final_result>>64),(uint64_t)final_result);
    // Then "4 distinct entry" cases:
    int is_minimal = 1;
    int new_one, new_y, new_z, new_last; // Useful for the sorting and minimal orbit elements.
    int short_multipliers[3];
    for (i = 0; i < y_power_count; i++) {
        y_coef_output[i] = 0;  // Reset the output array.
    }
    for (z = 3; z <= order_of_cyclotomics - 2; z++) {
        inv_z = inverses[z];
        for (y = 2; y < z; y++) {
            if (y > inv_z) {
                break; // No further y's are needed here!
            }
            // We want the minimum from:
            // [y,z,last]
            // [y*inv_z,inv_z,last*inv_z] (Sorted)
            // [y_inv,z*y_inv,last*y_inv] (Sorted)
            // [y*last_inv,z*last_inv,last_inv] (Sorted)
            last = (2 * order_of_cyclotomics - 1 - y - z) % order_of_cyclotomics;
            //printf("1, %d, %d, %d\n", y, z, last);
            if ((z >= last) || (last == sum_minus_1)) {
                continue;  // Order isn't preserved here, don't want it.
            }
            inv_y = inverses[y];
            inv_last = inverses[last];
            if ((y > inv_y) || (y > inv_last)) {
                continue; // More trivial checks for not being the smallest in the orbit.
            }
            short_multipliers[0] = inv_y;
            short_multipliers[1] = inv_z;
            short_multipliers[2] = inv_last;
            is_minimal = 1;
            for (i = 0; i < 3; i++) {
                // Get new values:
                new_one = (short_multipliers[i] * 1) % order_of_cyclotomics;
                new_y = (short_multipliers[i] * y) % order_of_cyclotomics;
                new_z = (short_multipliers[i] * z) % order_of_cyclotomics;
                new_last = (short_multipliers[i] * last) % order_of_cyclotomics;
                // Now sort the four new values:
                if(new_one>new_y) swap(&new_one,&new_y);
                if(new_z>new_last) swap(&new_z,&new_last);
                if(new_one>new_z) swap(&new_one,&new_z);
                if(new_y>new_last) swap(&new_y,&new_last);
                if(new_y>new_z) swap(&new_y,&new_z);
                // printf("%d %d %d %d\n", new_one, new_y, new_z, new_last);
                // And finally compare this to the previous:
                if (new_one != 1) {
                    printf("Something went horribly wrong!");
                    return 1;
                }
                if (new_y < y) {
                    //printf("%d %d %d %d > %d %d %d %d\n", 1, y, z, last, new_one, new_y, new_z, new_last);
                    is_minimal = 0;
                    break;
                } else {
                    if ((new_y == y) && (new_z < z)) {
                        //printf("%d %d %d %d > %d %d %d %d\n", 1, y, z, last, new_one, new_y, new_z, new_last);
                        is_minimal = 0;
                        break;
                    } else {
                        if ((new_y == y) && (new_z == z) && (new_last < last)) {
                            //printf("%d %d %d %d > %d %d %d %d\n", 1, y, z, last, new_one, new_y, new_z, new_last);
                            is_minimal = 0;
                            break;
                        }
                    }
                }
            }
            if (is_minimal == 1) {
                setCoordinates(base_exponents, 0, 1, y, z, last); // Gotta count 4 distinct 5-tuples.
                //printf("Gotten through!! 1, %d, %d, %d\n", y, z, last);
                computeProductValueWithoutReset(base_exponents, y_coef_output);
            }
        }
    }
    addToFinalResultWithMultiplier(y_coef_output, 120);
    //printf("Hex after 1 zero:\t\t%016llx%016llx \n",(uint64_t)(sum_bound>>64),(uint64_t)sum_bound);
    printf("Done 1 zero.\n");

    // ***** Finally, no zero possibilities: *****
    // Special cases first:
    setCoordinates(base_exponents, 1, 1, 1, 1, order_of_cyclotomics - 4); // This is there twice (4+1).
    computeProductValue(base_exponents, y_coef_output);
    addToFinalResultWithMultiplier(y_coef_output, 5);
    setCoordinates(base_exponents, 1, 1, 1, (order_of_cyclotomics - 3) / 2, (order_of_cyclotomics - 3) / 2); // This is there twice (6+4).
    computeProductValue(base_exponents, y_coef_output);
    addToFinalResultWithMultiplier(y_coef_output, 10);
    setCoordinates(base_exponents, 1, 1, 1, order_of_cyclotomics - 2, order_of_cyclotomics - 1); // This is there thrice (12+4+4).
    computeProductValue(base_exponents, y_coef_output);
    addToFinalResultWithMultiplier(y_coef_output, 20);
    //printf("Hex result: %016llx%016llx \n",(uint64_t)(final_result>>64),(uint64_t)final_result);
    // Then triple 1s cases:
    for (i = 0; i < y_power_count; i++) {
        y_coef_output[i] = 0;  // Reset the output array.
    }
    for (z = 2; z <= (order_of_cyclotomics - 5) / 2; z++) {
        setCoordinates(base_exponents, 1, 1, 1, z, order_of_cyclotomics - 3 - z); // This is there thrice (12+4+4).
        computeProductValueWithoutReset(base_exponents, y_coef_output);
    }
    addToFinalResultWithMultiplier(y_coef_output, 20);
    //printf("Hex result: %016llx%016llx \n",(uint64_t)(final_result>>64),(uint64_t)final_result);
    // Then double 1's cases with another duplicate:
    // Better - Rather single 1 and double duplicate!
    inv_last = inverses[2]; // Useful to have easily available.
    for (i = 0; i < y_power_count; i++) {
        y_coef_output[i] = 0;  // Reset the output array.
    }
    for (z = 2; z <= sum_minus_1; z++) {
        last = ((2*order_of_cyclotomics - 1 - z - z) * inv_last) % order_of_cyclotomics;
        if ((last == 1) || (last <= z)) {
            continue;  // Skip, this was counted already.
        }
        setCoordinates(base_exponents, 1, z, z, last, last); // This is there thrice (12+12+6).
        computeProductValueWithoutReset(base_exponents, y_coef_output);
    }
    addToFinalResultWithMultiplier(y_coef_output, 30);
    //printf("Hex result: %016llx%016llx \n",(uint64_t)(final_result>>64),(uint64_t)final_result);
    // Then double 1s cases with rest distinct:
    for (i = 0; i < y_power_count; i++) {
        y_coef_output[i] = 0;  // Reset the output array.
    }
    for (z = 3; z <= order_of_cyclotomics - 2; z++) {
        for (y = 2; y < z; y++) {
            last = (2*order_of_cyclotomics - 2 - y - z) % order_of_cyclotomics;
            if (z < last) {
                setCoordinates(base_exponents, 1, 1, y, z, last); // This is there quarce (24+12+12+12).
                computeProductValueWithoutReset(base_exponents, y_coef_output);
            }
        }
    }
    addToFinalResultWithMultiplier(y_coef_output, 60);
    //printf("Hex before 5 distinct:\t\t%016llx%016llx \n",(uint64_t)(sum_bound>>64),(uint64_t)sum_bound);
    printf("Done all except 5 distinct.\n");

    // Lastly, all distinct, that is in a separate function:
    DWORD worker_ids[WORKER_COUNT];
    HANDLE cubic_threads[WORKER_COUNT];
    // Set up proper multi-threaded space for computation:
    accum_mutex = CreateMutexW(NULL, FALSE, NULL);
    task_mutex = CreateMutexW(NULL, FALSE, NULL);
    last_not_done_task = 2;
    thread_task_limit = order_of_cyclotomics / 7;
    printf("Breakpoint = %d.\n",thread_task_limit);
    InitializeSynchronizationBarrier(&barrier, WORKER_COUNT + 1, -1);

    for(i = 0; i < WORKER_COUNT; i++) {
        // Create worker threads to begin execution on its own.
        cubic_threads[i] = CreateThread(NULL, 0, taskPicker, NULL, 0, &worker_ids[i]);
    }
    // Do the rest ("easy") values yourself:
    for(x = thread_task_limit; x <= order_of_cyclotomics - 4; x++) {
        processXEqualTo(x);
    }
    printf("Finished easy work.\n");
    // ... And then join the others in the work:
    taskPicker();

    // Clean-up everything and exit:
    for(i = 0; i < WORKER_COUNT; i++) {
        CloseHandle(cubic_threads[i]);
    }
    CloseHandle(accum_mutex);
    CloseHandle(task_mutex);
    DeleteSynchronizationBarrier(&barrier);
    clock_t toc = clock();
    __uint128_t check_sum_bound = 0;
    __uint128_t divisible_by_5_bound_check = 0;
    printf("Powers of y coefficients (in hex!!):\n");
    for (i = 0; i < y_power_count; i++) {
        printf("%d\t\t%016llx%016llx\n", i, (uint64_t)(final_result[i]>>64),(uint64_t)final_result[i]);
        check_sum_bound += 2 * final_result[i];
    }
    check_sum_bound -= final_result[60];
    printf("\n--------------------------------------------------------------------------------\n\n");
    for (i = 0; i < 61; i+=5) {
        printf("%016llx%016llx ", (uint64_t)(final_result[i]>>64),(uint64_t)final_result[i]);
        divisible_by_5_bound_check += 2 * final_result[i];
    }
    divisible_by_5_bound_check -= final_result[60];
    printf("\n\nElapsed: %f seconds\n", (double)(toc - tic) / CLOCKS_PER_SEC);
    //printf("Hex result (NOT divided!):\t%016llx%016llx \n",(uint64_t)(sum_bound>>64),(uint64_t)sum_bound);
    printf("Check for all (NOT divided!):\t%016llx%016llx \n",(uint64_t)(check_sum_bound>>64),(uint64_t)check_sum_bound);
    printf("Divisible by 5 (NOT divided!):\t%016llx%016llx \n",(uint64_t)(divisible_by_5_bound_check>>64),(uint64_t)divisible_by_5_bound_check);
    return 0;
}

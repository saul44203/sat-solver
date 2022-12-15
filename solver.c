#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#include "quicksort.h"
#include "cnf.h"
#include "stack.h"

unsigned V, C, L;     // Number of (V)ariables, (C)lauses and (L)iterals
unsigned DEPTH;       // Depth of vars structure
unsigned VERBOSE_LVL;
bool F_HEURISTIC;

unsigned* cls_idxs;	     // Clause indexes
int*      clss; 	     // Clause literals
unsigned* var_clss_idxs; // Variable indexes
int*      var_clss;      // Clauses per variable
bool*     vars;		     // Variable states
bool*     var_pref_val;  // Variable preferred first assignation values
unsigned* srtd_var_idxs; // Sorted variable indices
bool*     clss_sat;	     // Clause satisfability states
stack_t   prop_vars;     // Variables to be propagated
stack_t   ass_vars;      // Stack with assigned variables
stack_t   sat_clss;      // Stack with satisfied clauses 

long unsigned ps, ucs, cls, cfs, clvl, pvs, slvs; // Number of propagation
                                                  // loop iterations, unit
                                                  // clause propagations,
                                                  // conflicts, cumulative
                                                  // level (for mean level of
                                                  // solution/conflict) and
                                                  // pure variables


/*
 * Desc: Checks if all clauses are (or not) satisfied based on variable state
 * Return: T if all clauses are satisfied, F otherwise
 */
bool test(void) {
    for (unsigned i=0; i<C; i++) {
        unsigned sum = 0;

        for (unsigned j=cls_idxs[i]; j<cls_idxs[i+1]; j++) {
            int lit = clss[j];
            bool var = vars[abs(lit)-1];

            sum += ((var==T) == (lit>0));
        }

        if (sum == 0)
            return F;
    }
    return T;
}


/*
 * Desc: Checks if all clauses are satisfied by iterating over `clss_sat`
 * Return: T if all are, F otherwise
 */
bool all_sat(void) {
    for (unsigned i=0; i<C; i++)
        if (clss_sat[i] == F)
            return F;
    return T;
}


/*
 * Desc: Performs unit propagation by searching for clauses in `clss` that only
 * have one literal unassigned (known as unit clauses)
 * Return: F if contradiction was found and X when no further propagation can
 * be done
 */
bool unit_prop(unsigned lvl, unsigned d_var_idx) {
    stk_clear(&prop_vars);
    stk_push(&prop_vars, d_var_idx-(lvl==0));

    int v;
    while ((v=stk_pop(&prop_vars)) != 0) {
        unsigned start_cls = (v == -1) ? 0:var_clss_idxs[v-1];
        unsigned end_cls = (v == -1) ? C:var_clss_idxs[v];

        for (unsigned c=start_cls; c<end_cls; c++) { // For each clause
            unsigned cls_idx = abs(var_clss[c]);
            unsigned i = (v == -1) ? c:cls_idx-1;
            bool cls_sat = F;

            if (clss_sat[i] == T) // Skip if clause is already SAT
                continue; 
            
            if (v > 0) {
                assert(vars[v-1] != X);
                if ((vars[v-1]==T) == (var_clss[c]>0)) { // Skip if v SATs it
                    clss_sat[i] = T;
                    stk_push(&sat_clss, cls_idx);
                    continue;
                }
            }

            int unass_lit = 0;
            unsigned n_ass_vars = 0;

            unsigned start_idx = cls_idxs[i];
            unsigned end_idx = cls_idxs[i+1];
            unsigned clss_size = end_idx - start_idx;

            for (unsigned j=start_idx; j<end_idx; j++) { // For each lit
                int lit = clss[j];
                bool var = vars[abs(lit)-1];

                if (var != X) { // Already propagated variable
                    n_ass_vars++;
                    cls_sat = ((var==T) == (lit>0)); // Check if lit is T
                    if (cls_sat == T) { // Skip if T
                        clss_sat[i] = T;
                        stk_push(&sat_clss, cls_idx);
                        break; 
                    }
                } else // Remember last unassigned lit
                    unass_lit = lit; 
            }

            cls++;

            if (cls_sat == T) // Go to next clause if current one is satisfied
                continue;     
            
            if (n_ass_vars == clss_size) // Conflict if all variables that form
                return F;                // the clause are assigned and the
                                         // clause itself is not satisfied

            if (n_ass_vars == (clss_size-1)) { // Clause is unit
                unsigned var_idx = abs(unass_lit);
                bool val = (unass_lit > 0) ? T:F; // Set var to T/F
                vars[var_idx-1] = val;
                stk_push(&ass_vars, -var_idx);

                stk_push(&prop_vars, var_idx);
                clss_sat[i] = T;
                stk_push(&sat_clss, cls_idx);
                ucs++;
            }
        }
        ps++;
    }
    return X;
}


/*
 * Desc: Picks the first unassigned variable in `vars`
 * Return: The index of the unassigned variable or V if there isn't one
 */
unsigned pick_var(unsigned start) {
    for (unsigned i=start; i<V; i++)
        if (vars[i] == X)
            return i+1;

    return 0;
}


/*
 * Desc: Undoes changes in `vars` and `clss_sat` reestablishing coherence with
 * the last level of decision utilising `ass_vars` and `sat_clss` stacks as
 * logs of changes of the firsts, respectively
 */
void backtrack(unsigned d_var_idx) {
    int var_idx, cls_idx;

    // Unassign all forcefully assigned variables
    while ((var_idx = stk_pop(&ass_vars)) < 0)
        vars[abs(var_idx)-1] = X;

    // Unmark no longer satisfied clauses
    while ((cls_idx = stk_pop(&sat_clss)) > 0)
        clss_sat[cls_idx-1] = F;

    // Return if no variables left to backtrack
    if (var_idx == 0)
        return;

    // Reached decision variable
    assert((unsigned)var_idx == d_var_idx);
    vars[var_idx-1] = X;
}



/*
 * Desc: Implements the solver's recursive algorithm
 * Return: lvl if problem is SAT and F if UNSAT
 */
int solve(unsigned lvl, unsigned var_idx) {
    if (lvl >= DEPTH) {
        printf("[*] Max DEPTH reached\n");
        exit(EXIT_FAILURE);
    }

    slvs++;

    bool up_state = unit_prop(lvl, var_idx);
    if (up_state == F) { // Conflict
        cfs++;
        clvl += lvl;
        return F;
    }

    if (all_sat() == T)
        return lvl;

    var_idx = pick_var(var_idx);
    if (var_idx == 0) // Return F if there're no more unassigned variables
        return F;

    if (VERBOSE_LVL == lvl)
        printf("Variable %d selected\n", var_idx);

    // Copy vars and clss_sat and assign selected var to preferred value
    stk_push(&sat_clss, -(lvl+1));
    vars[var_idx-1] = var_pref_val[var_idx-1];
    stk_push(&ass_vars, var_idx);
    int s = solve(lvl+1, var_idx);
    if (s == F)
        backtrack(var_idx);
    else
        return s;

    // Try again with negation of preferred value
    stk_push(&sat_clss, -(lvl+1));
    vars[var_idx-1] = -1*var_pref_val[var_idx-1];
    stk_push(&ass_vars, var_idx);
    s = solve(lvl+1, var_idx);
    if (s == F)
        backtrack(var_idx);
    return s;
}


int main(int argc, char* argv[]) {
    if (argc <= 1)
        exit(EXIT_FAILURE);

    if (argc > 2)
        F_HEURISTIC = (argv[2][0] == 'y') ? T:F;
    else
        F_HEURISTIC = T;

    printf("[*] F_HEURISITC: %c\n", (F_HEURISTIC == T) ? 'T':'F');

    unsigned* var_pn_fs;
    read_cnf(argv[1], &cls_idxs, &clss, &var_pn_fs, &V, &C, &L);
    printf("[*] V=%u C=%u L=%u\n", V, C, L);

    unsigned* var_tf;
    calc_var_tf(&var_tf, &var_pn_fs, V);

    if (argc > 3)
        DEPTH = strtoul(argv[3], NULL, 0);
    else
        DEPTH = V;
    printf("[*] DEPTH: %u\n", DEPTH);

    if (argc > 4)
        VERBOSE_LVL = strtoul(argv[3], NULL, 0);
    else
        VERBOSE_LVL = -1;

    printf("[*] Allocating %lf MiB for clss_sat\n", DEPTH*(C/1048576.0));
    clss_sat = calloc(C, sizeof(bool));
    memset(clss_sat, F, C);

    printf("[*] Allocating %lf MiB for vars\n", V/1048576.0);
    vars = calloc(V, sizeof(bool));
    memset(vars, X, V);
    
    var_pref_val = calloc(V, sizeof(bool));
    srtd_var_idxs = calloc(V, sizeof(unsigned));
    if (F_HEURISTIC == T) {
        pvs = apply_heuristic(&vars, &clss, &var_pref_val, &var_pn_fs, &var_tf,
                              &srtd_var_idxs, V, L);
        free(var_pn_fs);
    } else {
        memset(var_pref_val, T, V);
        for (unsigned i=0; i<V; i++)
            srtd_var_idxs[i] = i;
    }

    calc_var_clss(&var_clss_idxs, &var_clss, &cls_idxs, &clss, &var_tf, V, C, L);
    free(var_tf);

    stk_init(&prop_vars, V);
    stk_init(&ass_vars, V);
    stk_init(&sat_clss, C+V);
    int lvl = solve(0, 0);
    printf("[*] Stats: slvs=%lu cfs=%lu cls=%lu ps=%lu ucs=%lu lvl=%d pvs=%lu lvl_cf=%.2f\n",
            slvs, cfs, cls, ps, ucs, lvl, pvs, (double)clvl/cfs);
    printf("%s\n", (lvl >= 0) ? "SAT":"UNSAT");

    if (lvl >= 0) { // Solution found
        bool tst = test();
        printf("%s\n", (tst == T) ? "TEST OK":"TEST NOK");

        for (unsigned i=1; i<=V; i++) { // Print solution
            unsigned idx = srtd_var_idxs[i-1];
            printf("%d ", (vars[idx] == T) ? i:-i);
        }
        printf("\n");
    }
}

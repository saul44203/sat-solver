#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#include "quicksort.h"
#include "cnf.h"

/* T/F=true/false, X=undefined/unassigned */
typedef enum {T=1, F=-1, X=0} bool; // Custom boolean typedef

unsigned V, C, L;     // Number of (V)ariables, (C)lauses and (L)iterals
unsigned DEPTH;       // Depth of vars structure
unsigned VERBOSE_LVL;

unsigned* cls_idxs;	     // Clauses indexs
int*      clss; 	     // Clauses
bool*     vars;		     // Variables
bool*     var_pref_val;  // Variable prefered first assignation value
unsigned* var_pn_fs;     // Variable +/- frequencies
unsigned* srtd_var_idxs; // Sorted variable indices

long unsigned ps, ucs, cls, cfs, clvl, pvs, slvs; // Number of propagation loop
                                                  // iterations, unit clause
                                                  // propagations, conflicts,
                                                  // cumulative level (for mean
                                                  // level of solution/conflict)
                                                  // and pure variables


/*
 * Desc: Checks if all clauses are (or not) satisfied based on variable state
 * Return: T if all clauses are satisfied, F otherwise
 */
bool test(unsigned lvl) {
    for (unsigned i=0; i<C; i++) {
        unsigned sum = 0;

        for (unsigned j=cls_idxs[i]; j<cls_idxs[i+1]; j++) {
            int lit = clss[j];
            bool var = vars[lvl*V + abs(lit)-1];

            sum += ((var==T) == (lit>0));
        }

        if (sum == 0)
            return F;
    }
    return T;
}


/*
 * Desc: Performs unit propagation by searching for clauses in `clss` that only
 * have one literal unassigned (also called unit clauses)
 * Return: F if contradiction was found, T if all clauses are satisfied and X
 * when no further propagation can be done
 */
bool unit_prop(unsigned lvl) {
    bool propagate = T;
    bool all_sat;

    while (propagate == T) { // repeat until no more propagation can be done
        ps++;
        propagate = F;
        all_sat = T;

        for (unsigned i=0; i<C; i++) { // For each clause
            bool cls_sat = F;
            int unass_lit = 0;
            unsigned n_ass_vars = 0;
            cls++;

            unsigned start_idx = cls_idxs[i];
            unsigned end_idx = cls_idxs[i+1];
            unsigned clss_size = end_idx - start_idx;

            for (unsigned j=start_idx; j<end_idx; j++) { // For each lit
                int lit = clss[j];
                bool var = vars[lvl*V+abs(lit)-1];

                if (var != X) { // Already propagated variable
                    n_ass_vars++;
                    cls_sat = ((var==T) == (lit>0));
                    if (cls_sat == T) // Check if lit is T
                        break; // Skip if T
                } else // Remember last unassigned lit
                    unass_lit = lit; 
            }

            if (cls_sat == T) // Go to next clause if current one is satisfied
                continue;     
            
            all_sat = X;

            if (n_ass_vars == clss_size) // Conflict if all variables that form
                return F;                // the clause are assigned and the
                                         // clause itself is not satisfied

            if (n_ass_vars == (clss_size-1)) {  // Clause is unit
                unsigned var_idx = abs(unass_lit)-1;
                bool val = (unass_lit > 0) ? T:F; // Set var to T/F
                vars[lvl*V+var_idx] = val;
                propagate = T;
                ucs++;
            }
        }
    }

    return all_sat;
}


/*
 * Desc: Picks the first unassigned variable in `vars`
 * Return: The index of the unassigned variable or V if there isnt't one
 */
unsigned pick_var(unsigned lvl, unsigned start) {
    for (unsigned i=start; i<V; i++)
        if (vars[lvl*V+i] == X)
            return i+1;

    return 0;
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
    
    bool up_state = unit_prop(lvl);
    if (var_idx>0 && up_state==F) { // Conflict
        cfs++;
        clvl += lvl;
        return F;
    }

    if (up_state == T)
        return lvl;

    var_idx = pick_var(lvl, var_idx);
    if (var_idx == 0) // Return F if there're no more unassigned variables
        return F;

    if (VERBOSE_LVL == lvl)
        printf("Variable %d selected\n", var_idx);

    // Copy vars[lvl]->vars[lvl+1] and assign selected var to preferred value
    memcpy(vars+(lvl+1)*V, vars+lvl*V, sizeof(bool)*V);
    vars[(lvl+1)*V+var_idx-1] = var_pref_val[var_idx-1];
    int s = solve(lvl+1, var_idx);
    if (s != F)
        return s;

    // Try again with negation of preferred value
    memcpy(vars+(lvl+1)*V, vars+lvl*V, sizeof(bool)*V);
    vars[(lvl+1)*V+var_idx-1] = -1*var_pref_val[var_idx-1];
    return solve(lvl+1, var_idx);
}


/*
 * Desc: Reorders variables heuristically to prioritize the decision of the
 * pure/most frequent ones and calculates the most frequent variable polarity of
 * each one to also heuristically prioritize its assignation value on decision
 * Return: Nothing
 */
void apply_heuristic(void) {
    unsigned var_tf[V], var_tf_idxs[V];

    for (unsigned i=0; i<(2*V); i+=2) { 
        unsigned f = var_pn_fs[i] + var_pn_fs[i+1]; // Calculate total var freq
        if (var_pn_fs[i]==0 || var_pn_fs[i+1]==0) {
            f = UINT_MAX; // Set max freq to pure variables 
            pvs++;
        }
        var_tf[i/2] = f; 
        var_tf_idxs[i/2] = i/2;  
    }

    quicksort(var_tf, var_tf_idxs, 0, V-1);
    
    for (unsigned i=0; i<V; i++) // Get sorted ordering
        srtd_var_idxs[var_tf_idxs[i]] = i;
    for (unsigned i=0; i<V; i++) // Get prefered assignation value
        var_pref_val[srtd_var_idxs[i]] = (var_pn_fs[2*i] >= var_pn_fs[2*i+1]) ? T:F;
    for (unsigned i=0; i<pvs; i++) // Assign pure variables
        vars[i] = var_pref_val[i];

    for (unsigned i=0; i<L; i++) { // Replace literals in clauses
        int lit = clss[i];
        unsigned var_idx = abs(lit)-1;
        clss[i] = ((-1)*(lit<0)+(lit>0))*(srtd_var_idxs[var_idx]+1);
    }
}


int main(int argc, char* argv[]) {
    if (argc <= 1)
        exit(EXIT_FAILURE);

    read_cnf(argv[1], &cls_idxs, &clss, &var_pn_fs, &V, &C, &L);
    printf("[*] V=%u C=%u L=%u\n", V, C, L);

    if (argc > 2)
        DEPTH = strtoul(argv[2], NULL, 0);
    else
        DEPTH = V;
    printf("[*] DEPTH: %u\n", DEPTH);

    if (argc > 3)
        VERBOSE_LVL = strtoul(argv[3], NULL, 0);
    else
        VERBOSE_LVL = -1;

    printf("[*] Allocating %lf MiB for vars\n", DEPTH*(V/1048576.0));
    vars = calloc(V*DEPTH, sizeof(bool));
    memset(vars, X, V*DEPTH);

    srtd_var_idxs = calloc(V, sizeof(unsigned));
    var_pref_val = calloc(V, sizeof(bool));
    apply_heuristic();
    free(var_pn_fs);

    int lvl = solve(0, 0);
    printf("[*] Stats: slvs=%lu cfs=%lu cls=%lu ps=%lu ucs=%lu lvl=%d pvs=%lu lvl_cf=%.2f\n",
            slvs, cfs, cls, ps, ucs, lvl, pvs, (double)clvl/cfs);
    printf("%s\n", (lvl >= 0) ? "SAT":"UNSAT");

    if (lvl >= 0) { // Solution found
        bool tst = test(lvl);
        printf("%s\n", (tst == T) ? "TEST OK":"TEST NOK");

        for (unsigned i=1; i<=V; i++) { // Print solution
            unsigned idx = srtd_var_idxs[i-1];
            printf("%d ", (vars[lvl*V+idx] == T) ? i:-i);
        }
        printf("\n");
    }
}

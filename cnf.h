#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "bool.h"

void read_cnf(char* file, unsigned** cls_idxs, int** clss, bool** vars,
              unsigned** var_pn_fs, unsigned** var_clss_idxs, int** var_clss,
              unsigned** srtd_var_idxs, bool** var_pref_val, long unsigned* pvs,
              unsigned* V, unsigned* C, unsigned* L, bool H) {
    // Open cnf file
    FILE* f = fopen(file, "r");

    // Get file size
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    rewind(f);

    // Read whole file to buffer
    char* cnf = calloc(size, sizeof(char));
    fread(cnf, 1, size, f);
    fclose(f);

    // Read number of vars and number of clausules
    long i = 0;
    while (    cnf[i]   != 'p' 
            || cnf[i+1] != ' '
            || cnf[i+2] != 'c' 
            || cnf[i+3] != 'n'
            || cnf[i+4] != 'f') { i++; }
    i+=5;
    char* ptr = cnf+i;
    *V = strtol(ptr, &ptr, 10);
    *C = strtol(ptr, &ptr, 10);
    i += ptr - (cnf+i);

    // Allocate memory to store clause indexs
    *cls_idxs = calloc(*C+1, sizeof(unsigned));
    
    // Count total number of literals and assign clause indexs
    *L = 0;
    unsigned c = 1;
    int n = i;
    while (n < size) {
        if (cnf[n] == '-' || ('1' <= cnf[n] && cnf[n] <= '9')) {
            while (cnf[n] == '-' || ('0' <= cnf[n] && cnf[n] <= '9'))
                n++;
            (*L)++;
        } else if (cnf[n] == '0') {
            (*cls_idxs)[c] = *L;
            c++;
        }
        n++;
    }

    // Read literals and calculate variable frequency by polarity
    *clss = calloc(*L, sizeof(int));
    *var_pn_fs = calloc(2*(*V), sizeof(unsigned));

    n = 0;
    while (ptr < (cnf+size)) {
        if (*ptr=='-' || ('1'<=*ptr && *ptr<='9')) {
            int lit = strtol(ptr, &ptr, 10);
            unsigned var_idx = abs(lit)-1;
            (*clss)[n++] = lit;
            (*var_pn_fs)[2*var_idx] += (lit>0);
            (*var_pn_fs)[2*var_idx+1] += (lit<0);
        }
        ptr++;
    }
    
    // Calculate total var frequency for heuristic
    unsigned var_tf[*V], var_tf_idxs[*V];
    *vars = calloc((*V)*(*V), sizeof(bool));
    for (unsigned i=0; i<2*(*V); i+=2) { 
        unsigned pf = (*var_pn_fs)[i];
        unsigned nf = (*var_pn_fs)[i+1];
        unsigned tf = pf + nf;
        var_tf[i/2] = tf; 
        var_tf_idxs[i/2] = i/2;  
    }
    
    if (H == T) // Apply frequency heuristic
        quicksort(var_tf, var_tf_idxs, 0, *V-1);
    
    // Get sorted ordering
    *srtd_var_idxs = calloc(*V, sizeof(unsigned));
    for (unsigned i=0; i<*V; i++)
        (*srtd_var_idxs)[var_tf_idxs[i]] = i;

    // Replace literals in clauses
    for (unsigned i=0; i<*L; i++) {
        int lit = (*clss)[i];
        unsigned var_idx = abs(lit)-1;
        (*clss)[i] = ((-1)*(lit<0)+(lit>0))*((*srtd_var_idxs)[var_idx]+1);
    }

    // Get prefered assignation value and assign pure variables
    *var_pref_val = calloc(*V, sizeof(bool));
    for (unsigned i=0; i<*V; i++) {
        unsigned var_idx = (*srtd_var_idxs)[i];
        unsigned pf = (*var_pn_fs)[2*i];
        unsigned nf = (*var_pn_fs)[2*i+1];
        bool pref_val = (pf >= nf) ? T:F; 
        (*var_pref_val)[var_idx] = pref_val;
        if (pf==0 || nf==0) {
            (*vars)[var_idx] = pref_val;
            (*pvs)++;
        }
    }
    
    // Calculate indexs for var_clss structure
    unsigned CF = 0;
    *var_clss_idxs = calloc(*V+1, sizeof(unsigned));
    for (unsigned i=1; i<=*V; i++) {
        //unsigned var_idx = var_tf_idxs[i-1];
        //CF += (*var_pn_fs)[2*var_idx] + (*var_pn_fs)[2*var_idx+1];
        CF += var_tf[i-1];
        (*var_clss_idxs)[i] = CF;
    }
    assert(CF == *L);

    // Store positive and negative variable ocurrencies in clauses
    *var_clss = calloc(*L, sizeof(int));
    for (unsigned i=0; i<*C; i++) {
        unsigned start_idx = (*cls_idxs)[i];
        unsigned end_idx = (*cls_idxs)[i+1];
        for (unsigned j=start_idx; j<end_idx; j++) {
            int lit = (*clss)[j];
            unsigned idx = (*var_clss_idxs)[abs(lit)-1];
            while ((*var_clss)[idx] != 0)
                idx++;
            (*var_clss)[idx] = (lit > 0) ? (i+1):-(i+1);
        }
    }

    free(cnf);
}

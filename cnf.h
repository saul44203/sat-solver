#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "bool.h"

void read_cnf(char* file, unsigned** cls_idxs, int** clss, unsigned** var_pn_fs,
              unsigned* V, unsigned* C, unsigned* L) {
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

    free(cnf);
}

void calc_var_tf(unsigned** var_tf, unsigned** var_pn_fs, unsigned V) {
    // Calculate total var frequency
    *var_tf = calloc(V, sizeof(unsigned));
    for (unsigned i=0; i<2*V; i+=2) { 
        unsigned pf = (*var_pn_fs)[i];
        unsigned nf = (*var_pn_fs)[i+1];
        unsigned tf = pf + nf;
        (*var_tf)[i/2] = tf;
    }
}


unsigned apply_heuristic(int** clss, bool** var_pref_val,
                         unsigned** var_pn_fs, unsigned** var_tf,
                         unsigned** srtd_var_idxs, unsigned V, unsigned L) {
    // Build index vector of var_tf
    unsigned var_tf_idxs[V];
    for (unsigned i=0; i<V; i++)
        var_tf_idxs[i] = i;
    
    // Sort var_tf and var_tf_idxs
    quicksort(*var_tf, var_tf_idxs, 0, V-1);

    // Get sorted ordering vector
    for (unsigned i=0; i<V; i++)
        (*srtd_var_idxs)[var_tf_idxs[i]] = i;

    // Replace literals in clauses
    for (unsigned i=0; i<L; i++) {
        int lit = (*clss)[i];
        unsigned var_idx = abs(lit)-1;
        (*clss)[i] = ((-1)*(lit<0)+(lit>0))*((*srtd_var_idxs)[var_idx]+1);
    }

    // Get prefered assignation value and assign pure variables
    unsigned pvs = 0;
    for (unsigned i=0; i<V; i++) {
        unsigned var_idx = (*srtd_var_idxs)[i];
        unsigned pf = (*var_pn_fs)[2*i];
        unsigned nf = (*var_pn_fs)[2*i+1];
        bool pref_val = (pf >= nf) ? T:F;
        (*var_pref_val)[var_idx] = pref_val;
        if (pf==0 || nf==0)
            pvs++;
    }

    return pvs;
}


void calc_var_clss(unsigned** var_clss_idxs, int** var_clss,
                   unsigned** cls_idxs, int** clss, unsigned** var_tf,
                   unsigned V, unsigned C, unsigned L) {
    // Calculate indexs for var_clss structure
    unsigned CF = 0;
    *var_clss_idxs = calloc(V+1, sizeof(unsigned));
    for (unsigned i=1; i<=V; i++) {
        //unsigned var_idx = var_tf_idxs[i-1];
        //CF += (*var_pn_fs)[2*var_idx] + (*var_pn_fs)[2*var_idx+1];
        CF += (*var_tf)[i-1];
        (*var_clss_idxs)[i] = CF;
    }
    assert(CF == L);

    // Store positive and negative variable ocurrencies in clauses
    *var_clss = calloc(L, sizeof(int));
    for (unsigned i=0; i<C; i++) {
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
}

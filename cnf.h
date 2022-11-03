#include <stdlib.h>
#include <string.h>

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

    // Allocate memory for clause and variable-clause array
    *clss = calloc(*L, sizeof(int));
    *var_pn_fs = calloc(2*(*V), sizeof(unsigned));

    // Calculate variable frequency by polarity
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

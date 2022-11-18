CFLAGS = -g -Wall -Wextra -march=native -fshort-enums -fno-inline
solver: solver.c cnf.h quicksort.h stack.h bool.h makefile
	gcc $(CFLAGS) solver.c -o solver

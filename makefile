CFLAGS = -g -Wall -Wextra -Ofast -march=native -fshort-enums -fno-inline
solver: solver.c cnf.h quicksort.h
	gcc $(CFLAGS) solver.c -o solver

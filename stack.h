#include <stdlib.h>

typedef struct {
    unsigned sz;
    unsigned sp;
    int* v;
} stack_t;

void stk_init(stack_t* st, unsigned size) {
    st->sz = size;
    st->sp = 0;
    st->v = calloc(st->sz, sizeof(int));
}

void stk_destroy(stack_t* st) {
    free(st->v);
}

void stk_clear(stack_t* st) {
    st->sp = 0;
}

void stk_push(stack_t* st, int i) {
    if (st->sp < st->sz)
        st->v[st->sp++] = i;
}

int stk_pop(stack_t* st) {
    if (st->sp > 0)
        return st->v[--st->sp];
    return 0;
}

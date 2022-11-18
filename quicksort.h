int partition(unsigned* v, unsigned* s, int l, int h) {
    int i = l-1;
    unsigned p = v[h];
    unsigned t;

    for (int j=l; j<h; j++) {
        if (v[j] >= p) {
            i++; 

            t = v[i];
            v[i] = v[j];
            v[j] = t;

            t = s[i];
            s[i] = s[j];
            s[j] = t;
        }
    }

    t = v[i+1];
    v[i+1] = v[h];
    v[h] = t;

    t = s[i+1];
    s[i+1] = s[h];
    s[h] = t;

    return i+1;
}

void quicksort(unsigned* v, unsigned* s, int l, int h) {
    if (l < h) {
        int idx = partition(v, s, l, h);
        quicksort(v, s, l, idx-1);
        quicksort(v, s, idx+1, h);
    }
}

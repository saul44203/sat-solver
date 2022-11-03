int partition(const unsigned* v, unsigned* s, int l, int h) {
    int i = l-1;
    unsigned p = v[s[h]];
    unsigned t;

    for (int j=l; j<h; j++) {
        if (v[s[j]] >= p) {
            i++; 
            t = s[i];
            s[i] = s[j];
            s[j] = t;
        }
    }

    t = s[i+1];
    s[i+1] = s[h];
    s[h] = t;

    return i+1;
}

void quicksort(const unsigned* v, unsigned* s, int l, int h) {
    if (l < h) {
        int idx = partition(v, s, l, h);
        quicksort(v, s, l, idx-1);
        quicksort(v, s, idx+1, h);
    }
}

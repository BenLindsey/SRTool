// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    int x;

    x = +(3 == 3);

    assert(x == 1);
    
    return 0;
}

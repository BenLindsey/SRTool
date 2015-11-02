// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    int x;

    x = 10 - -3;

    assert(x == 13);
    
    return 0;
}

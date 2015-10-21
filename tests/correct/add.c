// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    int i;

    i = 1 + 2;
    
    assert(i == 3);
    
    return 0;
}

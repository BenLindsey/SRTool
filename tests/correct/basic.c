// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    int i;

    i = 1;
    
    assert(i == 1);
    
    return 0;
}

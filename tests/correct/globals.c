// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int g;

int swagger() {

    int i;
    i = 1;

    g = 1;
    
    assert(g == 1);
    
    return 0;
}

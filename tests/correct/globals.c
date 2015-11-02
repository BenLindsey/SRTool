// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int g;

int swagger() {

    g = 1;
    assert(g == 1);
    
    return g;
}

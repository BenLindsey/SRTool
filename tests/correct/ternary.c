// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    int i;

    i = i > 5 ? 5 : i;
    
    assert(i == 5);
    
    return 0;
}

// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    int i;

    i = 10;

    i = i > 5 ? 5 : i;
    
    assert(i == 5);
    
    return 0;
}

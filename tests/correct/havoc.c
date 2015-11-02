// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int blarp() {
    int x;
    int y;
    
    y = x + 1;

    havoc x;

    y = x + 1;

    assert (y == x + 1);

    return 0;    
}

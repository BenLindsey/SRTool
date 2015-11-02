// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    assert(-2 < 5);
    
    return 0;
}

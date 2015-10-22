// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {

    int x;

    x = 1;
    assert( x == 0 );

    int z;

    if(x < 10) {
        assert(x < 10);
    }

    return z;
}

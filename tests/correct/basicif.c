// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger() {
    int x;
    x = 11;

    int z;

    if(x < 0) {
        z = 0;
        assert(x < 0);
        if( x < -10) {
            z = 0;
        } else {
            assert( x < 0 && x >= -10);
            z = 1;
        }
    } else {
        z = 2;
    }

    assert( z == 2 );

    return z;
}

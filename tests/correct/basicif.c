// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int swagger( int x ) {
    int z;

    if(x < 0) {
        z = 0;
    } else {
        z = 1;
    }

    return z;
}

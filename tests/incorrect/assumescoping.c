// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"


int test(int x)
{

    if (1) {
        assume x >= 2;
    }

    assert x >= 2 ;

    return x;
}

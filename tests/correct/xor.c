// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int test()
{
    int x;

    x = 1;


    assert(x ^ 2 == 3);

    return 0;
}

// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int test()
requires x > 0,
requires x < 10
{
    x = 5;

    assert(\old(x) + x > 5);

    return x;
}

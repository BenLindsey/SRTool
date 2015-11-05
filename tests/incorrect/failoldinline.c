// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int x;

int test()
requires x > 0,
requires x < 10
{
    x = 5;

    assert(\old(x) + x > 16);

    return x;
}

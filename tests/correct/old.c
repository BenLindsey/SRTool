// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int test()
ensures \result == \old(x) + 1
{
    x = x + 1;
    return x;
}

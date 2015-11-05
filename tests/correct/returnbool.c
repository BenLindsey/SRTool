// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;

int test()
    requires x + y == 1,
    ensures \result
{
    return x || y ;
}

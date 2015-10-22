// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int x)
    requires x > 0 && x < 10,
    ensures \result > 100
{
    return x + 100;
}

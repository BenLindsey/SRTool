// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int x)
    requires x > 0,
    ensures \result > 1
{
    return x * 2;
}

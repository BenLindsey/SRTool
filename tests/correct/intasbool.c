// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int test(int x)
requires x > 0
{
    if (x) {
        assert(1);
    } else {
        assert(0);
    }

    return 0;
}

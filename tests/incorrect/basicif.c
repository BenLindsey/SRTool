// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int getXOrZero(int x)
    requires x != 5,
    ensures \result >= 0,
    ensures \result != 5
{
    int z;

    if(x < 0) {
        z = 0;
    } else {
        assert(z != 1);
        z = x;
    }

    return z;
}

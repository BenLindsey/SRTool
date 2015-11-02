// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int iffy()
{
    int t;
    t = 10;

    if(1) {
        int u;
        u = 5;
    }

    assert(t == 10);
    return t;
}

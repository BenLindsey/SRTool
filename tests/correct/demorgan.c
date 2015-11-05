// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;

int test()
{
    assert((x && y) == !(!x || !y));

    return 0;
}

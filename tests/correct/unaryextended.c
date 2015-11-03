// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int test() {
    int x;

    x = ~!+~1 + ~!~-2;

    assert (x == -2);

    return 0;
}

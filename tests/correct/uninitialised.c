// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int x;

    assert (x >= -2147483648);
    assert (x <= 2147483647);
    return 0;
}

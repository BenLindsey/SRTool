// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int i;

    i = 2147483647;
    i = i + 1;

    assert (i == -2147483648);
    return 0;
}

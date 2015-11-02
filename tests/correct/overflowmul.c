// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int i;

    i = 2147483647;
    i = i * 5;

    assert (i == 2147483643);
    return 0;
}

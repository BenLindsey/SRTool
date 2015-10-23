// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {
    int x;

    assert (x > 0);
    return 0;
}

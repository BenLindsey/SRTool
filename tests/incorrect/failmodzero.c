// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    assert 5 % 0 == 0;

    return 0;

}

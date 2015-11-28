// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int i, int j)
    requires j >= 32 {

    assert(i >> j == 0);

    return 0;
}

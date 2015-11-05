// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int i, int j)
    requires j >= 32 {

    if(i >= 0) {
        assert(i >> j == 0);
    } else {
        assert(i >> j == -1);
    }

    return 0;
}

// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int test() {
    int x;

    x = 2;

    {
        x = 3;
    }

    assert x == 3;

    {
        int x;
        x = 5;
    }

    assert x == 3;

    {{{{
        x = 4;
    }}}}

    assert x == 4;

    return 0;
}

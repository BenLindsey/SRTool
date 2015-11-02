// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int test() {
    int y;
    int y1;

    y1 = 23;

    y = 1;
    y = 2;
    y = 3;
    y = 4;
    y = 5;
    y = 6;
    y = 7;
    y = 8;
    y = 9;
    y = 10;

    assert (y1 == 23);

    return 0;
}

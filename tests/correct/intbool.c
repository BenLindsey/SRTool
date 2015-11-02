// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int iffy()
{
    int i;
    i = 10;

    int y;

    y = 0;

    int z;

    z = -2;

    if ((i && z && !y) || -30) {
        assert (i + z == y + 8);
    } else {
        assert(0);
    }

    if (!0) {
        assert (!(z - z));
    }

    assert (i > y || !y);

    return 0;
}

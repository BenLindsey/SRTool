// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int iffy()
{
    int x;
    x = 5;

    if (x >= 5) {
        int x;
        x = 6;

        if (1) {
            x = -1;

            int y;
            y = 5;

            if (y == 5) {
                int y;
                y = 10;

            } else {
                y = 17;

                int x;
                x = 2;
            }

            assert (y == 17);
        }

        assert (x == -1);
    }

    assert (x == 5);
    return 0;
}

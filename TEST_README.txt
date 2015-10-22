To run the tests, you should use the lit framework.

* Installing lit

On a lab machine, do:

pip install --user --version=0.4.1 lit

This will cause lit to be installed at:

/path/to/homedir/.local/bin

Do:

/path/to/homedir/.local/bin/lit --version

to check whether lit has been installed successfully.  You may wish to
add /path/to/homedir/.local/bin to your PATH environment variable.  In
the instructions below, it is assumed that lit is on your path.

* Setting up your test environment

Copy the following files:

- CORRECT.expect
- INCORRECT.expect
- lit.site.cfg
- srtool

into the root directory of your solution.  If you are using the Java
skeleton, this should be the directory in which
antlr-4.5.1-complete.jar resides, which should be the same as the
directory where you compile your Java source files.  In particular,
the root directory should contain a "tool" sub-directory, containing
"SRTool.class".

Look at the srtool script.  This file takes two arguments.  The first
argument is expected to be the root directory of your solution.  The
second argument is expected to be the .c file to be analysed.  By
default, srtool sets your classpath appropriately, using the first
argument, then runs tool.SRTool on the given .c file.

* Running the tests using lit

From the root directory of your solution, navigate to the "tests"
sub-directory.  From there, do:

lit .

This should run the tests and print a report.

To run a specific test, do:

lit /path/to/specific/test.c

You can use the -v argument to lit to print verbose output.  This can
be useful if your tests are failing for configuration reasons, e.g. if
Z3 is not found on your path.

* Test expected outcomes

At the top of each .c file, you will see either:

// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

or:

// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

The first line in each case causes the srtool script to be invoked.
The first argument to the tool will be the root directory of your
solution; the second argument will be the name of the test program
itself.  The standard output of the srtool script will be redirected
to a file.  Afterwards, the diff utility will be executed to compare
the standard output of srtool with either CORRECT.expect or
INCORRECT.expect, depending on whether the test is expected to contain
a correct program or an incorrect program.  A test fails if diff
reports a difference.  So, for example, if your tool reports "CORRECT"
for a program that is expected to be correct (because '// RUN: %diff
%INCORECT "%t"' appears as the second line of the test), the test will
fail.

* Writing your own tests

You are encouraged to extend the given tests into a larger suite by
writing your own tests, using either '// RUN: %diff %INCORRECT "%t"'
or '// RUN: %diff %CORRECT "%t"' to indicate whether the test program
is expected to be correct or incorrect.

* Implementing timeouts

It is your responsibility to guard against your tool timing out,
e.g. due to infinite loops arising due to errors in your programming.
The lit framework will wait indefinitely for each test to terminate,
so to ensure that testing completes within a reasonable amount of
time, you should extend the srtool script so that it will
automatically kill your tool after 5 minutes (300 seconds).  You might
consider wrapping your tool in a Python script to achieve this, as
Python has libraries that provide support for killing processes after
time limits.

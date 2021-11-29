
To build the WDOSX binaries, the following Borland tools were used:

TASM.EXE v 3.1
TLINK.EXE v 3.01
TLINK32.EXE v 1.6.72.0
BCC32.EXE from BC++ 5.0
MAKE.EXE v 4.0

Using different versions and/or completely different tools might or might not
yield satisfactory results.

The build must be run from within a Win32 DOS box, it will _not_ run under
plain DOS. All of the above utilities must be in the search path (obviously).

To start the build, change into the BUILD.ME directory and type "make".

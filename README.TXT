---------------------------------------------------------------------------
                  Pascal Pro - free 32-bit pascal compiler
                                    http:\\www.cryogen.com\pascalpro
                                    email to: pascalpro@cryogen.com
---------------------------------------------------------------------------

1. Introduction.

2. Installation.

3. Compiling programs.
3.1. Compiling programs under WDOSX platform.
3.2. Compiling programs under DOS32 platform.

4. Used tools.
4.1. Supported assemblers.
4.2. Supported linkers.
4.3. Other tools.

5. Configuring compiler for you own platform.
5.1. Configuring command lines.
5.2. Configuring generated assembler output.


-------------------------------------------------------
1. Introduction.
  My English is not good, so excuse me for some mistakes in this description.
  This file contains some information about Pascal Pro compiler.
Pascal Pro is 32-bit free compile. You didn't need to pay for using that.
But if you'ld like you can send me $5-$50. In this case you have to contact
me and I'll say how you can do that.
  If you'll have some interesting ideas about Pascal Pro or you'll find
some errors also contact me, please.

-------------------------------------------------------
2. Installation.
  This version contains 3 packed files. For installation you must have
ZIP-unpacker, for example PKUNZIP.
  Unzip packages (with subdirectories) to a directory on your hard drive,
for example C:\PPRO\.
  For more comfortable usage you can add Pascal Pro directory to your path
search in autoexec.bat.

-------------------------------------------------------
3. Compiling programs.

  This version of Pascal Pro can produce programs for dos-protected mode
using two dos-extenders WDOSX and DOS32.
  To specify target which you'ld to use with your programs you have to
specify /Txxx parameter, where xxx is the target name.
  At first this target is default. But you can change default target by
setting /T switch in the ppro.cfg file.

3.1. Compiling programs under WDOSX platform.
  For compiling program under WDOSX platform you have to call ppro with
/TWDOSX parameter, for example
  ppro /TWDOSX hello.pas

3.2. Compiling programs under DOS32 platform.
  For compiling program under DOS32 platform you have to call ppro with
/TDOS32 parameter, for example
  ppro /TDOS32 hello.pas

-------------------------------------------------------
4. Used tools.
4.1. Supported assemblers.
4.2. Supported linkers.
4.3. Other tools.

-------------------------------------------------------
5. Configuring compiler for you own platform.
5.1. Configuring command lines.
5.2. Configuring generated assembler output.



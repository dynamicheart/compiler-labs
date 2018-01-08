# compiler-labs

### 要注意的地方（待完善的地方）

- codegen时候使用maxmum munch的方式，这里只做了最简单的几种，保证程序能够正常运行，x86寻址模式有很多种，组合也有很多种，如果要减少最后汇编的长度，可从此处着手。

- 在处理callee-saved寄存器的时候，使用了比较tricky的方法，就是在每个函数一开始的时候把x86三个callee-saved寄存器各自放入一个temp寄存器里面（三条move指令），函数返回之前再从temp寄存器读回（这样做的目的是用到callee-saved寄存器时只会在函数一开始时spill一次，而不会在每次使用时都spill，但如果只要求livess analysis正确，只需要在最后ret指令时use那三个callee-saved寄存器就行）。但这样做的结果是，比如，如果用到了esi，由于那三条move指令，可能将会导致esi被move到edi，edi被spill，实际上只需要把edi给spill，然后用edi就行了。

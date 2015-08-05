# fcd

**fcd** is a LLVM-based native program decompiler. It implements
[pattern-independent structuring][1] to provide a goto-free output (when
decompilation succeeds).

It uses [interpiler][2] to create a code generator from an x86 emulator, making
it (usually) very easy to add new instructions to the decompilable set.

fcd is still a work in progress. You can contribute by finding ways to produce
a more readable output or by tackling one of the issues that deserves a branch.

**This branch** exists for the purpose of implementing type inference in the
decompiler. The implementation is based on the [TIE technique][3]. This should
help clean up quite a few LLVM casts.

  [1]: http://www.internetsociety.org/doc/no-more-gotos-decompilation-using-pattern-independent-control-flow-structuring-and-semantics
  [2]: https://github.com/zneak/interpiler
  [3]: https://users.ece.cmu.edu/~dbrumley/pdf/Lee,%20Avgerinos,%20Brumley_2011_TIE%20Principled%20Reverse%20Engineering%20of%20Types%20in%20Binary%20Programs.pdf
My attempt at [ICFP Programming Contest 2014](http://icfpcontest.org/) using [PLT Redex](http://redex.racket-lang.org/)

* The ``compiler'' is in [code/lambda-compiler.rkt](https://github.com/philnguyen/lambdaman-redex/blob/master/code/lambda-compiler.rkt)
* The program itself is in [code/lambda-prog.rkt](https://github.com/philnguyen/lambdaman-redex/blob/master/code/lambda-prog.rkt)
* The generated assembly is in [solution/lambdaman.gcc](https://github.com/philnguyen/lambdaman-redex/blob/master/solution/lambdaman.gcc)

To dump the λ-man program to stdout:
> racket code/lambda-prog.rkt

I tried a minimax-like algorithm at first, but easily reached the Cycle Limit even at small depths.
I eventually crippled it into a naive method that checks out each of the four directions and see what happens
if I just go straight for a few steps.
The agent survives the maps for quite a while but sometimes has problems exploring new places, moving back and forth (temporarily).

# Catt - An infinity-categorical coherence typechecker

Catt is an implementation of a type system for coherence in
Grothendieck/Maltsiniotis style infinity categories, whose
theory is outline [here](http://arxiv.org/abs/1009.2331).

## Building

You will need the [bnfc converter](http://bnfc.digitalgrammars.com/)
to generate the syntax.  Follow the instructions on the site to
install the tool on your machine

1. Clone the repository
2. Run the "regen" script in the src directory
   to generate the grammar
3. In the repo directory, run "cabal build"

You can then try out some of the examples in the examples
directory.
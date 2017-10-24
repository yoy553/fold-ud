# fold-ud

The directory dual contains Coq scripsts (ver.8.6) discussed in the paper. 

Title : Program Equivalence by Generalization of Second Fold Duality
Author: Yosuke Yamamot and Chris Dutchyn


FoldLib.v  : Ltac script, Main-Abs and Sub-Abs (section 3)

MyLib.v    : Library for the project

cata.v     : List-catamorphisms  (section 2)

para.v     : List-paramorphisms  (section 4.1)
state.v    : State-computations (section 4.2) 

./Fact     : 
Fact.v     : factorial functions (section 1)

./Insert
Insert.v   : insert functions (section 4.1)

./Ref      : Two finger relocate function for a simple gc (section 4.2)
RefImp.v   : relocates function for a lanugage used in [1] and emplemented as
             an anser to one of exercises.
RefFold.v  : relocates function implemented by using 
             upward and downward unary recursion 
             

   [1] Benjamin C. Pierce, Chris Casinghino, Michael Greenberg, et al. 
           Software Foundations. http://www.cis.upenn.edu/~bcpierce/sf
           Mar 2011. 

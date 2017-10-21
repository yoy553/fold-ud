(**
<<
   Sections 
      - Dual_state
      - 

   Used by: 
      - fact_sep (SimpleFold/Fact.v). 
      - loop (SimpleFold/AppFoldLoop.v)
      - incrL/relocate (Ref/RefFold.v)

  [Pottier 2014] Pottier, Francois. loop (Dec 11, 2014), fpottier. 
                    https://github.com/fpottier/loop
  [Bird 2010]    Bird, Richard. Pearls of Functional Algorithm Design. Cambridge
                    University Press. 2010. 

>>
*)

  Require Export dual.FoldLib.
  Require Export Recdef.

  (* PUBLIC *)
  Inductive state S T :=
  | StNext: S -> state S T
  | StEnd: T -> state S T.
  
  Check StNext.

  Arguments StNext { S T } _.
  Arguments StEnd { S T } _.

  Section Dual_state.

    Context { S T B : Type }.
    Context { g_lt : S -> S -> Prop }.
    (* Context { e: B }. *) (* identity of the algebra *)
    Variable e:B.

    Variable z: T -> B -> B.
    Variable cr: S -> B -> B .
    Variable cl: B -> S -> B .
    Variable g: S -> state S T .

    Hypothesis wf_g_lt : well_founded g_lt.
    Hypothesis g_ind__onlyif__g_lt: forall s s',  g s = StNext s' ->
                                          g_lt s' s.

    Function stTransU 
             (seed: B)
             (s: S) {wf g_lt s} : B:=
      match (g s) with
        | StEnd t => z t seed 
        | StNext s' => cr s' (stTransU seed s')
      end. 
    Proof.
      intros. 
      apply g_ind__onlyif__g_lt.
      exact teq.
      exact wf_g_lt.
    Defined. 

    
    Function stTransD 
             (acc: B)
             (s: S) {wf g_lt s}: B :=
      match (g s) with
        | StEnd t => z t acc 
        | StNext s' => stTransD (cl acc s') s'
      end.
    Proof.
      intros. 
      apply g_ind__onlyif__g_lt.
      exact teq.
      exact wf_g_lt.
    Defined. 

    Hypothesis Associative: forall x y z, cr x (cl y z) = cl (cr x y) z.
    Hypothesis Unit: forall x, cr x e = cl e x. 

    Hypothesis Hoisting: forall x acc t, cr x (z t acc) = z t (cr x acc).

    Definition Meta_Lemma :=
      forall s c acc,  
        cr c (stTransD acc s) = stTransD (cr c acc) s.
    
    Lemma stTransU__stTransD: 
      forall s, 
        stTransU e s = stTransD e s.
    Proof.
      Main_Abs
        stTransD
        stTransU
        stTransD_equation            
        stTransU_equation            
        Associative
        Unit
        Hoisting
        Meta_Lemma
      .
    Qed. 

   
  End Dual_state.






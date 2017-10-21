(**
<<

  Sections
    - Dual_para: List-paramorphisms

     2016.01.27 v1.01  Added based on Dual_beta.v and Dual_hylo_para.v.

>>
*)


  Require Import Coq.Arith.Wf_nat.                 (* [lt_wf] *)
  Require Import Coq.Wellfounded.Inverse_Image.    (* [wf_inverse_image] *)
  
  Require Import dual.FoldLib.
  Require Export dual.MyLib.
  Require Import Recdef.




  Section Dual_para.
    Context { A B: Type }.

    Variable cr: (A * list A) -> B -> B.
    Variable cl: B -> (A * list A) -> B.
    Variable e: B.

    Definition g_lt (m1 m2: list A) := lt_length m1 m2.

    Definition g (m: list A) := m.

    Lemma g_lt_is_wf : well_founded g_lt.
    Proof. 
      apply lt_length_wf.
    Qed.

    Lemma g_ind__onlyif__g_lt:
      forall m x xs,
        g m = x::xs ->
        g_lt xs m.
    Proof. 
      intros * G.
      unfold g in G.
      subst m.
      unfold g_lt.
      unfold lt_length.
      simpl.
      auto.
    Qed. 

    Function paraU
           (seed: B)
           (m: list A) {wf g_lt m} : B:=
      match g m with
        | [] => seed
        | x::xs => cr (x, xs) (paraU seed xs)
      end. 
    Proof.    
      intros. 
      apply g_ind__onlyif__g_lt with (x:=x).
      now unfold g.
      exact g_lt_is_wf.
    Defined. 

    Function paraD
             (acc: B)
             (m: list A) {wf g_lt m}: B :=
      match g m with
        | [] => acc
        | x::xs => paraD (cl acc (x,xs)) xs
      end. 
    Proof.    
      intros. 
      apply g_ind__onlyif__g_lt with (x:=x).
      now unfold g.      
      exact g_lt_is_wf.
    Defined. 


    Hypothesis Associative: 
      forall x y z,
        cr x (cl y z) = 
        cl (cr x y) z.

    Hypothesis Unit:
      forall x, 
        cr x e = cl e x. 


    Lemma Hoisting : forall x:B, x = x.
    auto.
    Qed.

    Definition Meta_Lemma :=
      forall m xs x acc, 
        cr (x, xs) (paraD acc m) = 
        paraD (cr (x, xs) acc) m. 


    Lemma paraU__paraD:
      forall m, 
        paraU e m = paraD e m.
    Proof.

      Unset Ltac Debug. 
      
      Main_Abs
        paraD
        paraU
        paraD_equation             (* unaryDown_equation *)
        paraU_equation            (* unaryUp_equation *)
        Associative
        Unit
        Hoisting
        Meta_Lemma
      .
      Unset Ltac Debug.
    Qed. 

  End Dual_para.
    


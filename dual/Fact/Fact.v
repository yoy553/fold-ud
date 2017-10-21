(**
<<

>>
*)


  
  Fixpoint fact_aux (acc: nat) (n:nat):=
    match n with
      | O => acc
      | S n' => (fact_aux (acc*n) n')
    end.
  Functional Scheme fact_aux_ind := Induction for fact_aux Sort Prop.
  
  Definition fact_tr (n: nat) := fact_aux 1 n.


  Require Import Arith Ring.
  
  Lemma fact_aux_assoc: forall n acc m,
      m * (fact_aux acc n) = fact_aux (m*acc) n.
  Proof.
    intro n. 
    induction n as [| n']; intros. 
    - simpl.
      rewrite mult_comm.
      reflexivity.
    - simpl (fact_aux acc (S n')).
      rewrite IHn'.
      simpl.
      rewrite <- mult_assoc.      
      reflexivity.
  Qed.   

  
  Fixpoint fact_seed (seed n:nat):=
    match n with
      | O => seed
      | S n' => n * (fact_seed seed n')
    end.
  Functional Scheme fact_seed_ind := Induction for fact_seed Sort Prop.
  
  Theorem fact_seed__fact_aux: forall n acc,
      fact_seed acc n = fact_aux acc n.
  Proof.
    intros.
    functional induction (fact_seed acc n). 
    - simpl. reflexivity.
    - simpl (fact_aux acc (S n')).
      symmetry.
      rewrite mult_comm.
      rewrite <- fact_aux_assoc.
      rewrite IHn0.
      reflexivity.
  Qed. 
  
  Theorem fact_tr_div: forall n acc,
      n > 0 -> Nat.divide n (fact_aux acc n).
  Proof. 
    intros * Ngt0.
    destruct n as [| n'].
    - inversion Ngt0.
    - simpl.

  Restart. 
    intros * Ngt0.
    rewrite <- fact_seed__fact_aux.
    destruct n as [| n'].
    - inversion Ngt0.
    - unfold fact_seed; fold fact_seed. 
      apply Nat.divide_factor_l. 
  Qed.



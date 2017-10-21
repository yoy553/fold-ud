(**
<<

>>
*)


  Require Import dual.MyLib. 
  Require Import Recdef.  

  Fixpoint ins (k: nat) (m: list nat) :=
    match m with 
      | nil => [k]
      | x::xs => if k <=? x then k::m
                 else x::(ins k xs)
    end.

  Fixpoint ins_tr (k: nat) (m acc: list nat) :=
    match m with 
      | nil => acc ++ [k]
      | x::xs => if k <=? x then acc++(k::m)
                 else ins_tr k xs (acc++[x])
    end.

  Compute (ins 4 [2,3]).
  Compute (ins_tr 4 [2,3] []).

  Compute (ins 4 [3,5]).
  Compute (ins_tr 4 [3,5] []).

  Require Import dual.para.

  Definition cr_ins
             (k:nat) (a: nat * list nat) 
             (c: list nat -> list nat)
  : list nat -> list nat := 
    let (y, ys) := a in
      if k <=? y then 
        fun t => k::y::ys
      else 
        fun t => y::(c t).

  Definition cl_ins
             (k:nat) 
             (c: list nat -> list nat)
             (a: nat * list nat) 
  : list nat -> list nat := 
    let (y, ys) := a in
      if k <=? y then 
        fun t => c (k::y::ys)
      else 
        fun t => c (y::t).


  Definition g_ins (m: list nat) : option ((nat * list nat) * list nat)  :=
    match m with
      | [] => None
      | x::xs => Some ((x, m), xs) 
    end.

  Lemma g_ins_lt: 
      forall m (x: nat * list nat) xs, 
        g_ins m = Some (x, xs) -> lt_length xs m. 
    Proof. 
      intros.
      unfold g_ins in H.
      destruct m as [| y ys].
      - inversion H. 
      - injection H; intros Ys Y.
        subst; auto.
        unfold lt_length.
        simpl; auto with arith.
    Qed.  



  Definition insU' (k: nat) (m: list nat) :=
    paraU (cr_ins k)
          (fun t => t)
          m
  .  

  Lemma ins__insU': 
    forall k m, 
      ins k m = (insU' k m) [k].
  Proof.
    intros.
    induction m as [| x xs].
    - unfold insU'.
      rewrite paraU_equation.
      auto.
    - unfold insU'.
      rewrite paraU_equation.
      simpl.
      case (k <=? x).
      +
        reflexivity.
      +
        unfold insU' in IHxs.
        rewrite <- IHxs.
        reflexivity.
  Qed. 


  Definition insU (k: nat) (m: list nat) :=
    (paraU (cr_ins k)
           (fun t => t)
           m)
      [k]
  .

  
  Lemma ins__insU: 
    forall k m, 
      ins k m = insU k m.
  Proof.
    intros.
    induction m as [| x xs].
    - unfold insU.
      rewrite paraU_equation.
      auto.
    - unfold insU.
      rewrite paraU_equation.
      simpl.
      case (k <=? x).
      + reflexivity.
      + unfold insU in IHxs.
        rewrite IHxs.
        reflexivity.
  Qed. 


  Definition insD (k: nat) (m: list nat) :=
    (paraD (cl_ins k)
           (fun t => t)
           m)
      [k]
  .


  
  Definition second_duality_thm_1: 
    forall x y z k,
      (cr_ins k) x ((cl_ins k) y z) = 
      (cl_ins k) ((cr_ins k) x y) z.
  Proof. 
    intros [x xm] y [z zm] k.
    unfold cr_ins, cl_ins.
    case (k <=? x); case (k <=? z);
    reflexivity.
  Qed.       
  
  Definition second_duality_thm_2:
      forall x k, 
        (cr_ins k) x list_id = (cl_ins k) list_id x. 
  Proof.
    intros [x xm] k.
    unfold cr_ins, cl_ins.    
    case (k <=? x); reflexivity.
  Qed. 

    
  Theorem insU__insD:
    forall k m, 
      insU k m = insD k m.
  Proof.
    intros.
    unfold insU, insD.
    erewrite paraU__paraD.
    reflexivity.
    intros.
    apply second_duality_thm_1.
    intros.
    apply second_duality_thm_2.
  Qed. 

  
  
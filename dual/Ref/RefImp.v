(** 

    This file is an modificaion/extention of gc exercise from References.v
    of Software Foundation (Pierce 2012).
    It implements a toy gc (mark and compact), which is based on [2] (page 
    602-603) and also explained in [3] (chapter 3). 

<<

   [1] Benjamin C. Pierce, Chris Casinghino, Michael Greenberg 
           C\v{a}t\v{a}lin Hri\c{t}cu, Vilhelm Sjoberg and Brent Yorgey.
           Software Foundations. http://www.cis.upenn.edu/~bcpierce/sf
           July 2012. 
   [2] Knuth, Donald E. The Art of Computer Programming, Vol. 1: Fundamental 
           Algorithms. Addision-Wesley. Reading, MA. 1969.
   [3] Jones, Richard, Antony Hosking, and Eliot Moss. Garbage Collector 
           Handbook: The Art of Automatic Memory Management. CRC Press. 
           Boca Raton. 2012. 

>>
*)

  
  Require Export dual.MyLib.
  Require Export Recdef.
  Require Export Bool.
  Require Export List.
  Require Export Arith.
  Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

  (** Types *)

  Inductive ty : Type :=
  | ty_nat   : ty
  | ty_arrow : ty -> ty -> ty
  | ty_unit  : ty
  | ty_ref   : ty -> ty.

  (* ################################### *)


  (** [Module id] from Software Foundation 2012, Imp.v

   *)



    Inductive id : Type := 
      Id : nat -> id.

    Definition beq_id X1 X2 :=
      match (X1, X2) with
          (Id n1, Id n2) => beq_nat n1 n2
      end.

    Theorem beq_id_refl : 
      forall X,
        true = beq_id X X.
    Proof.
      intros. destruct X.
      apply beq_nat_refl.  
    Qed.

    Theorem beq_id_eq : 
      forall i1 i2,
        true = beq_id i1 i2 -> i1 = i2.
    Proof.
      intros i1 i2 H.
      destruct i1 as [n1]; destruct i2 as [n2].
      unfold beq_id in H.
      rewrite (beq_nat_true n1 n2); auto.
    Qed.

    Theorem beq_id_false_not_eq : 
      forall i1 i2,
        beq_id i1 i2 = false -> i1 <> i2.
    Proof.
      intros i1 i2 H. 
      destruct i1 as [n1]; destruct i2 as [n2].
      unfold beq_id in H.
      generalize dependent n2.
      generalize dependent n1.
      induction n1; destruct n2; simpl; intro H; try discriminate.
      apply IHn1 in H.
      intro Contr; inversion Contr.
      apply H; auto.
    Qed.

    (** Coq Art, page 255 *)

    Definition eq_dec (A: Type) := forall x y: A, {x = y}+{x <> y}.
    Lemma eq_dec_nat: eq_dec nat. unfold eq_dec. auto with arith. Qed.


    
    
    Theorem not_eq_beq_id_false : 
      forall i1 i2,
        i1 <> i2 -> beq_id i1 i2 = false.
    Proof.
      intros i1 i2 Neq.
      destruct i1 as [n1]; destruct i2 as [n2].
      unfold beq_id.
      destruct (eq_dec_nat n1 n2).
      - subst n1.
        apply False_ind.
        now apply Neq.
      - now apply Nat.eqb_neq. 
    Qed.

    Theorem beq_id_sym: 
      forall i1 i2,
        beq_id i1 i2 = beq_id i2 i1.
    Proof.
      intros i1 i2.
      destruct i1 as [n1]; destruct i2 as [n2].
      unfold beq_id.      
      apply Nat.eqb_sym. 
    Qed. 
  (** [] *)




  (** Terms *)

  Inductive tm  : Type :=
  | tm_var    : id -> tm
  | tm_app    : tm -> tm -> tm
  | tm_abs    : id -> ty -> tm -> tm
  | tm_nat    : nat -> tm
  | tm_succ   : tm -> tm
  | tm_pred   : tm -> tm
  | tm_add    : tm -> tm -> tm
  | tm_mult   : tm -> tm -> tm
  | tm_if0    : tm -> tm -> tm -> tm
  | tm_unit   : tm
  | tm_ref    : tm -> tm
  | tm_deref  : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc    : nat -> tm.



  (** IDs *)

  Definition _a := Id 1001.
  Definition _b := Id 1002.
  Definition _c := Id 1003.
  Definition _d := Id 1004.
  Definition _e := Id 1005.
  Definition _f := Id 1006.
  Definition _g := Id 1007.
  Definition _h := Id 1008.
  Definition _i := Id 1009.
  Definition _j := Id 1010.
  Definition _k := Id 1011.
  Definition _l := Id 1012.
  Definition _m := Id 1013.
  Definition _n := Id 1014.
  Definition _o := Id 1015.
  Definition _p := Id 1016.
  Definition _q := Id 1017.
  Definition _r := Id 1018.
  Definition _s := Id 1019.
  Definition _t := Id 1020.
  Definition _u := Id 1021.
  Definition _v := Id 1022.
  Definition _w := Id 1023.
  Definition _x := Id 1024.
  Definition _y := Id 1025.
  Definition _z := Id 1026.


  (* ################################### *)
  (** Values and Substitution *)

  Inductive value : tm -> Prop :=
  | v_abs  : forall x T t,
               value (tm_abs x T t)
  | v_nat : forall n,
              value (tm_nat n)
  | v_unit : 
      value tm_unit
  | v_loc : forall l,
              value (tm_loc l).

  Hint Constructors value.

  (** From Software Foundation Imp.v. 
   *)


  Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
    match t with
      | tm_var x'       => if beq_id x x' then s else t
      | tm_app t1 t2    => tm_app (subst x s t1) (subst x s t2)
      | tm_abs x' T t1  => if beq_id x x' then t else tm_abs x' T (subst x s t1)
      | tm_nat n        => t
      | tm_succ t1      => tm_succ (subst x s t1)
      | tm_pred t1      => tm_pred (subst x s t1)
      | tm_add t1 t2    => tm_add (subst x s t1) (subst x s t2)
      | tm_mult t1 t2   => tm_mult (subst x s t1) (subst x s t2)
      | tm_if0 t1 t2 t3 => tm_if0 (subst x s t1) (subst x s t2) (subst x s t3)
      | tm_unit         => t
      | tm_ref t1       => tm_ref (subst x s t1)
      | tm_deref t1     => tm_deref (subst x s t1)
      | tm_assign t1 t2 => tm_assign (subst x s t1) (subst x s t2)
      | tm_loc _        => t
    end.

  (* ###################################################################### *)

  Definition tm_seq t1 t2 := tm_app (tm_abs _x ty_unit t2) t1.

  Definition cell := (prod bool tm).

  Definition store := list cell.

  Notation "'|' m '|'" := (length m) (at level 50).

  Definition isLive (c: cell) := (fst c).
  Definition isFree (c: cell) := negb (isLive c).

  Lemma isLive_neg_isFree:
    forall c, isLive c = negb (isFree c).
  Proof. 
    intro c. unfold isLive, isFree. 
    now rewrite negb_involutive. 
  Qed. 

  Definition store_lookup (n:nat) (st:store): tm :=
    (snd (nth n st (false, tm_unit))).

  Definition store_lookup_cell (n:nat) (st:store): (bool * tm) :=
    (nth n st (false, tm_unit)).

  Fixpoint replace {A:Type} (n:nat) (x:A) (l:list (bool * A)) : list (bool * A) :=
    match l with
      | nil    => nil
      | h :: t => 
        match n with
          | O    => ((fst h), x) :: t
          | S n' => h :: replace n' x t
        end
    end.



  (** *** Fixpoint: [clearMarks] 

      This function is used to initialize the memory when program is to start. 
      Afterwords, [gc] clears the memory when finishing relocation. 
   **)

  Fixpoint clearMark(c: cell) : cell :=
    match c with 
      | (live, data) => (false, data) 
    end.

  
  Fixpoint clearMarks(s: store) : store :=
    match s with 
      | nil => []
      | e::s' => (clearMark e)::clearMarks s'
    end.
  
  Functional Scheme clearMarks_ind := Induction for clearMarks Sort Prop.


  Fixpoint findFree (m: store) (acc: store) :=
    match m with 
      | [] => None
      | x::xs => if (isFree x) then Some (acc, x, xs)
                 else findFree xs (acc++[clearMark x]) 
    end.                                      
  Functional Scheme findFree_ind := Induction for findFree Sort Prop.

  Fixpoint findFreeX_aux (m acc: store) (offset: nat):= 
    match m with 
      | [] => None
      | x::xs => if (isFree x) then Some (acc, offset, xs)
                 else findFreeX_aux xs (acc++[clearMark x]) (S offset)
    end.
  Functional Scheme findFreeX_aux_ind := Induction for findFreeX_aux Sort Prop.

  Definition findFreeX (m acc: store) := findFreeX_aux m acc 0.

  (*
  Definition findFreeX (m acc: store) := 
    let fix f (m acc: store) (offset: nat):= 
        match m with 
          | [] => None
          | x::xs => if (isFree x) then Some (acc, offset, xs)
                     else f xs (acc++[clearMark x]) (S offset)
        end
    in f m acc 0.
  *)

  Lemma findFree_reduces_list:
    forall m acc acc' x xs, 
      findFree m acc = Some (acc',x,xs) -> |xs| < |m|.
  Proof. 
    intros m acc.
    functional induction (findFree m acc); intros * FF; inversion FF.
    - simpl. omega. 
    - apply IHo in FF.
      simpl. 
      apply lt_trans with (m:=|xs|); auto.
  Qed.       


  Require Export dual.MyLib.
  Require Import dual.cata. 

  Fixpoint lastVal {A: Type} (m: list A) (d: A) := 
    match m with 
      | [] => d
      | x::xs => lastVal xs x
    end. 

  
  Definition delLast {A: Type} (m: list A) :=
    match rev_tr m [] with
      | [] => []
      | x::xs => rev_tr xs []
    end.

  Lemma delLast_len:
    forall {A: Type} (y: A) (ys: list A), 
   |delLast (y :: ys) | < |y :: ys |.
  Proof. 
    intros. 
    unfold delLast.
    rewrite <- rev__rev_tr.
    Check rev_length.
    name_term xxs (rev (y::ys)) REV_YYS.
    rewrite <- REV_YYS.
    destruct xxs as [| x xs].
    - simpl. auto with arith.
    - rewrite <- rev__rev_tr.
      assert (XXS_YYS: |x::xs| = |y::ys|).
      {
        rewrite REV_YYS.
        apply rev_length.
      }
      rewrite <- XXS_YYS.
      assert (REV_XXS: |rev xs| = |xs|) by apply rev_length.
      rewrite REV_XXS.
      simpl.
      auto with arith.
  Qed.


  Function scanLive (m: store) (acc: store) {measure length m} :=
    match m with
      | [] => None
      | y::ys => let x := lastVal m y in
                 let sx := delLast m in 
                 if (isLive x) then Some (sx, x, acc)
                 else scanLive sx (x::acc)
    end.
  Proof.
    intros.
    apply delLast_len.
  Qed. 


  Functional Scheme scanLive_ind := Induction for scanLive Sort Prop.


  Lemma scanLive_reduces_list:
    forall m acc sx x acc', 
      scanLive m acc = Some (sx, x, acc') -> |sx| < |m|.
  Proof. 
    intros m acc.
    functional induction (scanLive m acc); intros * FF; inversion FF.
    - apply delLast_len.
    - apply IHo in FF.
      apply lt_trans with (m:= |delLast (y :: ys) |); auto.
      apply delLast_len.
  Qed.       


  Function relocate_tr (m acc_l acc_r: store) (L: nat) {measure length m}:=
    match findFree m [] with
      | None => (acc_l ++ m ++ acc_r, L)
      | Some (m_l, _, m_r) => 
        match scanLive m_r [] with 
          | None => (acc_l ++ m ++ acc_r, L)
          | Some (m_m, y, m_r) => 
            let L' := L + |m_l| in
            relocate_tr m_m (acc_l ++ m_l ++ [y]) ([(false, tm_nat L')]++ m_r ++ acc_r) (L' + 1)
        end
    end. 
  Proof. 
    intros. 
    apply findFree_reduces_list in teq.
    apply scanLive_reduces_list in teq2. 
    apply lt_trans with (m:=(|m_r|)); assumption.
  Qed. 

  


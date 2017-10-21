(**
<<
>>
*)

  Require Import Coq.Arith.Wf_nat. 
  Require Import Coq.Wellfounded.Inverse_Image.

  Require Import dual.FoldLib.
  Require Import dual.state.
  Require Export dual.Ref.RefImp.
 
(**
  
<<
  Inductive state_rel: Type :=
    StRel: store           (* mem_live *)
           -> cell         (* vacant_cell *)
           -> store        (* mem_rmnd *)
           -> cell         (* live_cell *)
           -> store        (* mem_free *)
//           -> nat          (* previsou_addr *)
           -> nat          (* next_addr *)
           -> state_rel.
>>


  *)


  Inductive state_rel: Type :=
    StRel: store -> 
           cell -> 
           store -> 
           cell -> 
           store ->
           nat -> 
           state_rel.

 
  (*
  Inductive state_rel: Type :=
    (prod store (prod cell (prod store (prod store nat)))).
  *)
  Print state_rel.

  (** 
      - Dual_state.S === state_rel
      - Dual_state.B === store * store * nat
   *)

  Definition g_rel (s: state_rel) : state state_rel store:=
    match s with 
      | StRel _ _ mem_rmnd _ _ addr => 
    match findFree mem_rmnd [] with
      | None => StEnd mem_rmnd
      | Some (mem_live, free_offset, mem_rmnd') => 
    match scanLive mem_rmnd' [] with
      | None => StEnd mem_rmnd
      | Some (mem_rmnd'', live_cell, mem_free) =>
          let move_to := addr + |mem_live| in
          let vacant_cell := (false, tm_nat move_to) in
          StNext
            (StRel
               mem_live
               live_cell
               mem_rmnd''
               vacant_cell
               mem_free 
               (move_to + 1))
    end
    end
    end. 
  Check g_rel.

  Definition getMm (s: state_rel): store :=
    match s with StRel _ _ m _ _ _ => m end. 

  Definition cl_rel (acc: store * store) (s: state_rel): (store * store):=
    match s with
      | StRel mem_live live_cell mem_rmnd vacant_cell mem_free addr =>
        match acc with 
          | (acc_l, acc_r) =>  
            (acc_l++mem_live++[live_cell], [vacant_cell]++mem_free++acc_r)
        end
    end. 

  Definition cr_rel (s: state_rel) (acc: store * store): (store * store):=
    match s with
      | StRel mem_live live_cell mem_rmnd vacant_cell mem_free addr =>
        match acc with 
          | (acc_l, acc_r) =>  
            (mem_live++[live_cell]++acc_l, acc_r++[vacant_cell]++mem_free)
        end
    end. 

  Notation "x '+rep' y" := (cr_rel x y) (at level 60, right associativity).
  Notation "x '*rep' y" := (cl_rel x y) (at level 60, right associativity).

  Lemma Associative_rel: 
    forall x y z,
      cr_rel x (cl_rel y z) = cl_rel (cr_rel x y) z.
  Proof. 
    intros. 
    destruct x as [mlx cx mmx mrx Lx Lx']; simpl.
    destruct z as [mlz cz mmz mrz Lz Lz']; simpl.
    destruct y as [y1 y2].
    simpl.
    rewrite <- app_assoc. 
    rewrite <- app_assoc.
    rewrite app_comm_cons.
    reflexivity. 
  Qed. 

   
  Lemma Unit_rel:
    forall x, 
      cr_rel x ([],[]) = cl_rel ([],[]) x.
  Proof. 
    intros. 
    unfold cr_rel, cl_rel.
    destruct x as [s s'].
    simpl.
    rewrite app_nil_r.
    reflexivity. 
  Qed. 

  Definition z_rel (s: store) (acc: store * store): store * store:=
    match acc with 
      | (acc_l, acc_r) => (acc_l ++ s, acc_r)
    end.

  Lemma Hoisting_rel: 
    forall x acc t, cr_rel x (z_rel t acc) = z_rel t (cr_rel x acc).
  Proof. 
    intros. 
    unfold cr_rel. 
    destruct x as [ml_1 k_1 mm_1 j_1 mr_1 L_1].
    destruct acc as [acc_l acc_r].
    name_term acc (z_rel t (acc_l, acc_r)) ACC.
    rewrite <- ACC.
    destruct acc as [acc_l' acc_r'].
    unfold z_rel in *. 
    inversion ACC; clear ACC.
    subst. 
    simpl.
    rewrite <- app_assoc. 
    rewrite <- app_comm_cons. 
    reflexivity.
  Qed.


  Definition lt_mm (s' s: state_rel) := lt_length (getMm s') (getMm s).
  Lemma lt_mm_wf: well_founded lt_mm. 
  Proof.
    unfold lt_mm.
    unfold lt_length. 
    eapply wf_inverse_image. eapply lt_wf.
  Qed.

  Lemma g_rel_reduce: 
    forall s s',
      g_rel s = StNext s' -> lt_mm s' s.
  Proof. 
    intros * Gd; unfold lt_mm.
    unfold g_rel in Gd.
    unfold lt_length.
    destruct s as [ml x mm mr n];
      destruct s' as [ml' x' mm' mr' n'];
      simpl.
    remember (findFree mm []) as r_ff.
    destruct r_ff. 
    - destruct p. destruct p.
      symmetry in Heqr_ff. 
      apply findFree_reduces_list in Heqr_ff. 
      remember (scanLive l []) as r_sl.
      destruct r_sl.
      + destruct p. destruct p.
        symmetry in Heqr_sl.
        apply scanLive_reduces_list in Heqr_sl.
        inversion Gd.
        subst.
        omega.
      + inversion Gd.
    - inversion Gd.
  Qed. 


  
  Definition relocateD (m acc_l acc_r: store) (L: nat):=
    stTransD
      z_rel
      cl_rel
      g_rel
      lt_mm_wf
      g_rel_reduce
      (acc_l, acc_r)
      (StRel [] (false, tm_unit) m (false, tm_unit) [] L).    



  Definition relocateU (m: store) (L: nat):=
    stTransU
      z_rel
      cr_rel
      g_rel
      lt_mm_wf
      g_rel_reduce
      ([], [])
      (StRel [] (false, tm_unit) m (false, tm_unit) [] L).    



  
  Theorem relocateD__relocateU: 
    forall m L, 
      relocateD m [] [] L = relocateU m L.
  Proof.
    intros; unfold relocateD; unfold relocateU.
    symmetry. 
    apply stTransU__stTransD; auto.
    intros; apply Associative_rel.
    intros; apply Unit_rel.
    intros; apply Hoisting_rel.
  Qed. 







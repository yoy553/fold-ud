(**
<<
   This is a library of Ltac that shows equivalence between two implementations: 
   one is tail recurive, foldl-like, program and the other is inductive, foldr-like,
   program. 
>>

 *)



  Require Export List.


  Ltac f_functional_ind_FI_IH f FI IH :=
    idtac "f_functional_ind_FI_IH: start";
    idtac f; 
    match goal with
    | |- context [f ?X ?Y ?Z] => idtac "f_functional_ind_FI_IH: f X Y Z";
                                 functional induction (f X Y Z) as [* FI| * FI IH]      
    | |- context [f ?X ?Y] => idtac "f_functional_ind_FI_IH: f X Y";
                              functional induction (f X Y) as [* FI| * FI IH]
    | |- context [f ?X] => idtac "f_functional_ind_FI_IH: f X";
                           functional induction (f X) as [* FI| * FI IH]
    | |- context [f] => idtac "f_functional_ind_FI_IH: f";
                        functional induction (f) as [* FI| * FI IH]
    end. 

  Ltac f_equation_r_unfold f f_equation :=
    let XXX := fresh "XXX" in  
    match goal with
    | |- ?X = _ => set (XXX:=X)
    end; 
    match goal with
    | |- _ = f ?X ?Y ?Z => rewrite f_equation                                      
    | |- _ = f ?X ?Y => rewrite f_equation
    | |- _ = f ?X  => rewrite f_equation
    | |- _ = f     => rewrite f_equation

    end;
    unfold XXX; clear XXX.

  
  
    Ltac clear_context_except2_tac 
       T1 T2 :=
    idtac;
    repeat match goal with 
             | [H: ?X|- _ ] => 
               match type of T1 with
                 | X => idtac
                 | _ => 
                   match type of T2 with
                     | X => idtac 
                     | _ => clear H
                   end
               end
           end.


  Ltac Sub_Abs
         linD
         linD_equation
         Associative
         Hoisting
    :=
  idtac "sub_01"    ; intros
; idtac "sub_02"    ; let FI := fresh "FI" in
                      let IH := fresh "IH" in
                      f_functional_ind_FI_IH linD FI IH
; idtac "sub_03"    ; intros
; idtac "sub_04"    ; f_equation_r_unfold linD linD_equation
; idtac "sub_05"    ; rewrite FI
; idtac "sub_06"    ; trivial || (rewrite <- Associative; apply IH).
 
   Ltac Main_Abs
        linD
        linU 
        linD_equation
        linU_equation 
        Associative
        Unit
        Hoisting
        Meta_Lemma
     :=
                      intros
; idtac "main_01"    ; let FI := fresh "FI" in
                       let IH := fresh "IH" in
                      f_functional_ind_FI_IH linU FI IH
; idtac "main_02"    ; f_equation_r_unfold linD linD_equation
; idtac "main_03"    ; rewrite FI
; idtac "main_04"    ; assert (FLHD: Meta_Lemma)
                       by (clear_context_except2_tac
                             Associative
                             Hoisting;
                           unfold Meta_Lemma;
                           Sub_Abs
                             linD linD_equation
                             Associative
                             Hoisting)
                            
; idtac "main_05"   ; let tac1 := trivial in
                      let tac2 := 
                          (
 idtac "main_06";           rewrite IH; clear IH; clear FI; 
 idtac "main_07";           intros; rewrite <- Unit; trivial;
                            apply FLHD)

                      in tac1 || tac2.
    

    Unset Ltac Debug.

 

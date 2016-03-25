(**************************************************************************)
(*  This is part of IMP-STATES-EXCEPTIONS, it is distributed under the    *)
(*       terms  of the GNU Lesser General Public License version 3        *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Axioms Derived_co_Pairs
        Derived_co_Products Proofs Functions IMPEX_to_COQ.
Set Implicit Arguments.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
Require Setoid.

Module Make(Import M: Memory.T).
  Module Export IMPEX_ProofsExp := IMPEX_to_COQ.Make(M).

 Lemma lemma1: forall (b: bool) (f g: Cmd), 
      (EPURE rw (dCmd f)) -> (EPURE rw (dCmd g)) -> 
      {{IFB const b 
          THEN (IFB const b THEN f ELSE g ENDIF) 
        ELSE g 
        ENDIF}}
      ===
      {{IFB const b 
          THEN f 
        ELSE g 
        ENDIF}}.
 Proof.
      intros. simpl. induction b. rewrite (@copair_true rw);  [reflexivity| edecorate | edecorate].
      setoid_rewrite (@copair_false rw); [reflexivity | edecorate | edecorate | edecorate | edecorate].
 Qed. 


 Lemma lemma2: forall (x: Loc),
	{{x ::= (const 2) ;;
	  WHILE ((loc x) << (const 11))
	    DO (x ::= ((loc x) +++ (const 4)))
	  ENDWHILE}}
	===
	{{x ::= (const 14)}}.
 Proof.
    intro x. simpl.
      do 3 setoid_rewrite <- assoc at 1. rewrite commutation_lookup_constant_update.
      do 4 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 3. rewrite imp3. 
 (*first loop iteration*)
      do 2 setoid_rewrite <- assoc. setoid_rewrite assoc at 1. 
    cut (
      (copair
      (lpi (pbl o (tpure chklt o pair (lookup x) (constant 11)))
      (update x o (tpure add o pair (lookup x) (constant 4)))
      o (update x o (tpure add o pair (lookup x) (constant 4)))) id o coproj1)
                          ===
      (lpi (pbl o (tpure chklt o pair (lookup x) (constant 11)))
      (update x o (tpure add o pair (lookup x) (constant 4)))
      o (update x o (tpure add o pair (lookup x) (constant 4))))
    ).
    intro H1. rewrite H1. 
      do 3 setoid_rewrite <- assoc at 1. rewrite commutation_lookup_constant_update. 
      do 3 setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2.
      rewrite imp1. simpl. setoid_rewrite <- assoc at 2.
      setoid_rewrite assoc. do 2 setoid_rewrite <- assoc at 1.
      rewrite interaction_update_update.
 (*second loop iteration*)
    rewrite imp_loopiter.
    do 3 setoid_rewrite <- assoc at 1. rewrite commutation_lookup_constant_update.
    do 3 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 2. rewrite imp3.
      rewrite H1.
      do 3 setoid_rewrite <- assoc at 1. rewrite commutation_lookup_constant_update. 
      do 3 setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2.
      rewrite imp1. simpl. setoid_rewrite <- assoc at 2.
      setoid_rewrite assoc. do 2 setoid_rewrite <- assoc at 1.
      rewrite interaction_update_update.
 (*third loop iteration*)
    rewrite imp_loopiter.
    do 3 setoid_rewrite <- assoc at 1. rewrite commutation_lookup_constant_update.
    do 3 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 2. rewrite imp3. 
      rewrite H1.
      do 3 setoid_rewrite <- assoc at 1. rewrite commutation_lookup_constant_update. 
      do 3 setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2.
      rewrite imp1. simpl. setoid_rewrite <- assoc at 2.
      setoid_rewrite assoc. do 2 setoid_rewrite <- assoc at 1.
      rewrite interaction_update_update.
 (*fourth loop iteration*)
  rewrite imp_loopiter.
    do 3 setoid_rewrite <- assoc at 1. rewrite commutation_lookup_constant_update.
    do 3 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 2. rewrite imp2.
      rewrite (@ss_lcopair_eq _ _ _ rw); [| edecorate].
  rewrite idt. reflexivity.
  simpl. reflexivity. easy. easy. 
      apply (@swtoss _ _ rw _ _); try edecorate.
      rewrite (@sw_lcopair_eq _ _ _ rw); try edecorate.  
  easy. easy.
 Qed.

 Lemma lemma3: forall (x y: Loc), forall (e: EName), x <> y ->
       {{x ::= (const 1) ;;
         (y ::= (const 20)) ;;
         TRY(WHILE (const true)
               DO(IFB ((loc x) <<= (const 0))
                    THEN (THROW e)
                  ELSE(x ::= ((loc x) +++ (const (-1))))
                  ENDIF)
              ENDWHILE)
         CATCH e => (y ::= (const 7))}}
       ===
       {{x ::= (const 0) ;;
         (y ::= (const 7))}}.
 Proof.
    intros. simpl. unfold try_catch.
      apply (@swtoss _ _ rw). apply is_comp. apply is_ro_rw, is_pure_ro, is_downcast.
      edecorate. edecorate.
 (*tackling downcast*)
      transitivity( ((copair id ((update y o constant 7) o untag e) o coproj1)
      o (copair
        (lpi (pbl o constant true)
           (copair (throw () e)
              (update x o (tpure add o pair (lookup x) (constant (-1))))
            o (pbl o (tpure chkle o pair (lookup x) (constant 0))))
         o (copair (throw () e)
              (update x o (tpure add o pair (lookup x) (constant (-1))))
            o (pbl o (tpure chkle o pair (lookup x) (constant 0))))) id
      o (pbl o constant true)))
      o ((update y o constant 20) o (update x o constant 1))).
      apply (@pswsubs _ _ _  rw) .
        apply swsym, sw_downcast. unfold pure_id. split. edecorate. reflexivity.
    setoid_rewrite commutation_update_update; [| exact H| exact H].
      setoid_rewrite <- assoc at 1.
 (*first loop iteration*)
    rewrite (@copair_true rw); [ | unfold throw; apply is_comp; [edecorate| apply is_comp; [ apply is_copair;
      [decorate | decorate | edecorate]| edecorate ]]| decorate ].      
    do 3 setoid_rewrite assoc at 3.
    setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 4.
    rewrite commutation_lookup_constant_update.
    do 2 setoid_rewrite  assoc at 3. do 2 setoid_rewrite <- assoc at 6.
    rewrite imp2. setoid_rewrite <- assoc at 6.
    rewrite (@ss_lcopair_eq _ _ _ rw).
    setoid_rewrite <- assoc at 4. do 3 setoid_rewrite <- assoc at 4.
    rewrite commutation_lookup_constant_update.
    do 3 setoid_rewrite assoc at 3. setoid_rewrite <- assoc at 5.
    rewrite imp1. 
    simpl. setoid_rewrite <- assoc at 5. setoid_rewrite <- assoc at 4.
    rewrite interaction_update_update.
 (*second loop iteration*)
    rewrite imp_loopiter.
    rewrite (@copair_true rw); [ | unfold throw; apply is_comp; [edecorate| apply is_comp; [ apply is_copair;
      [decorate | decorate | edecorate]| edecorate ]]| decorate ].    
    setoid_rewrite <- assoc at 3. do 3 setoid_rewrite assoc at 3.
    setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 4.
    rewrite commutation_lookup_constant_update.
    do 2 setoid_rewrite  assoc at 3. do 2 setoid_rewrite <- assoc at 6.
    rewrite imp3. setoid_rewrite <- assoc at 6.
    rewrite <- pbl_true. rewrite (@copair_true rw); [| decorate| edecorate].
    setoid_rewrite assoc at 1. setoid_rewrite assoc at 2. setoid_rewrite assoc at 2.
    setoid_rewrite <- assoc at 2. setoid_rewrite <- assoc at 1.
    setoid_rewrite <- assoc at 1.
 (*an exception is thrown -> quitting the loop in the second loop iteration*)
    unfold throw. rewrite PPT.
    setoid_rewrite assoc. setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 3.
    cut(coproj1 o (@empty unit) === coproj2).
      intro H1. rewrite H1.
      rewrite assoc. rewrite (@ss_lcopair_eq _ _ _ rw).
      setoid_rewrite assoc. setoid_rewrite <- assoc at 2.
      transitivity (((update y o constant 7) o id) o
      ((update x o constant 0) o (update y o constant 20))).
      repeat setoid_rewrite <- assoc. setoid_rewrite assoc. apply swrepl. reflexivity.
      setoid_rewrite assoc at 1. apply (@pswsubs _ _ _ rw).
      apply eax1. unfold pure_id. 
      split. decorate. reflexivity. rewrite ids. setoid_rewrite <- assoc at 3.
      rewrite commutation_update_update. setoid_rewrite assoc at 1.
      rewrite interaction_update_update.
      rewrite commutation_update_update. reflexivity.
      exact H. auto. decorate.
      repeat apply is_comp. unfold lpi. 
    (*1st cut*)
    setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate].
    decorate.
    easy. decorate. easy.
 Qed.

End Make.

(**************************************************************************)
(*  This is part of IMP-STATES-EXCEPTIONS, it is distributed under the    *)
(*       terms  of the GNU Lesser General Public License version 3        *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			                 Burak Ekici, Damien Pous.                        *)
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
      {{IFB bconst b 
          THEN (IFB bconst b THEN f ELSE g ENDIF) 
        ELSE g 
        ENDIF}}
      ===
      {{IFB bconst b 
          THEN f 
        ELSE g 
        ENDIF}}.
 Proof.
      intros. case_eq b; intros; simpl.
      - rewrite !(@copair_true rw); try edecorate. easy.
      - rewrite !(@copair_false rw); try edecorate. easy.
 Qed.

 Lemma lemma2: forall (x: Loc),
	{{x ::= (aconst 2) ;;
	  WHILE ((var x) << (aconst 11))
	    DO (x ::= ((var x) +++ (aconst 4)))
	  ENDWHILE}}
	===
	{{x ::= (aconst 14)}}.
 Proof.
    intro x. simpl.
      do 3 setoid_rewrite <- assoc at 1. rewrite CLUC.
      do 4 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 3. rewrite imp3. 
 (*first loop iteration*)
      do 2 setoid_rewrite <- assoc. setoid_rewrite assoc at 1. 
    cut (
      (copair
      (lpi (pbl o (tpure chklt o pair (lookup x) (constant 11)))
      (update x o (tpure add o pair (lookup x) (constant 4)))
      o (update x o (tpure add o pair (lookup x) (constant 4)))) id o (pbl o constant true))
                          ===
      (lpi (pbl o (tpure chklt o pair (lookup x) (constant 11)))
      (update x o (tpure add o pair (lookup x) (constant 4)))
      o (update x o (tpure add o pair (lookup x) (constant 4))))
    ).
    intro H1. rewrite H1. 
      do 3 setoid_rewrite <- assoc at 1. rewrite CLUC. 
      do 3 setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2.
      rewrite imp1. simpl. setoid_rewrite <- assoc at 2.
      setoid_rewrite assoc. do 2 setoid_rewrite <- assoc at 1.
      rewrite IUU.
 (*second loop iteration*)
    rewrite imp_loopiter.
    do 3 setoid_rewrite <- assoc at 1. rewrite CLUC.
    do 3 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 2. rewrite imp3.
      rewrite H1.
      do 3 setoid_rewrite <- assoc at 1. rewrite CLUC. 
      do 3 setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2.
      rewrite imp1. simpl. setoid_rewrite <- assoc at 2.
      setoid_rewrite assoc. do 2 setoid_rewrite <- assoc at 1.
      rewrite IUU.
 (*third loop iteration*)
    rewrite imp_loopiter.
    do 3 setoid_rewrite <- assoc at 1. rewrite CLUC.
    do 3 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 2. rewrite imp3. 
      rewrite H1.
      do 3 setoid_rewrite <- assoc at 1. rewrite CLUC. 
      do 3 setoid_rewrite assoc at 1. setoid_rewrite <- assoc at 2.
      rewrite imp1. simpl. setoid_rewrite <- assoc at 2.
      setoid_rewrite assoc. do 2 setoid_rewrite <- assoc at 1.
      rewrite IUU.
 (*fourth loop iteration*)
  rewrite imp_loopiter.
    do 3 setoid_rewrite <- assoc at 1. rewrite CLUC.
    do 3 setoid_rewrite assoc at 1.
      do 2 setoid_rewrite <- assoc at 2. rewrite imp2.
      rewrite !(@copair_false rw); try edecorate.
      rewrite idt. reflexivity. easy. easy. easy.
      rewrite !(@copair_true rw); try edecorate.
    easy. easy.
 Qed.

 Lemma lemma3: forall (x y: Loc), forall (e: EName), x <> y ->
       {{x ::= (aconst 1) ;;
         (y ::= (aconst 20)) ;;
         TRY(WHILE (ttrue)
               DO(IFB ((var x) <<= (aconst 0))
                    THEN (THROW e)
                  ELSE(x ::= ((var x) +++ (aconst (-1))))
                  ENDIF)
              ENDWHILE)
         CATCH e => (y ::= (aconst 7))}}
       ===
       {{x ::= (aconst 0) ;;
         (y ::= (aconst 7))}}.
 Proof.
    intros. simpl. unfold try_catch.
      apply (@swtoss _ _ rw). apply is_comp. apply is_ro_rw, is_pure_ro, is_downcast.
      edecorate. edecorate.
 (*tackling downcast*)
      transitivity( ((copair id ((update y o constant 7) o untag e) o in1)
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
    setoid_rewrite CUU; [| exact H| exact H].
      setoid_rewrite <- assoc at 1.
 (*first loop iteration*)
    rewrite (@copair_true rw); [ | unfold throw; apply is_comp; [edecorate| apply is_comp; [ apply is_copair;
      [decorate | decorate | edecorate]| edecorate ]]| decorate ].
    do 3 setoid_rewrite assoc at 3.
    setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 4.
    rewrite CLUC.
    do 2 setoid_rewrite  assoc at 3. do 2 setoid_rewrite <- assoc at 6.
    rewrite imp2. setoid_rewrite <- assoc at 6.
      rewrite !(@copair_false rw); try edecorate.
    setoid_rewrite <- assoc at 4. do 3 setoid_rewrite <- assoc at 4.
    rewrite CLUC.
    do 3 setoid_rewrite assoc at 3. setoid_rewrite <- assoc at 5.
    rewrite imp1. 
    simpl. setoid_rewrite <- assoc at 5. setoid_rewrite <- assoc at 4.
    rewrite IUU.
 (*second loop iteration*)
    rewrite imp_loopiter.
    rewrite (@copair_true rw); [ | unfold throw; apply is_comp; [edecorate| apply is_comp; [ apply is_copair;
      [decorate | decorate | edecorate]| edecorate ]]| decorate ].
    setoid_rewrite <- assoc at 3. do 3 setoid_rewrite assoc at 3.
    setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 4.
    rewrite CLUC.
    do 2 setoid_rewrite  assoc at 3. do 2 setoid_rewrite <- assoc at 6.
    rewrite imp3. setoid_rewrite <- assoc at 6.
    rewrite (@copair_true rw); [| decorate| edecorate].
    setoid_rewrite assoc at 1. setoid_rewrite assoc at 2. 
    setoid_rewrite assoc at 2.
    setoid_rewrite <- assoc at 2. setoid_rewrite <- assoc at 1.
    setoid_rewrite <- assoc at 1.
 (*an exception is thrown -> quitting the loop in the second loop iteration*)
    unfold throw. rewrite PPT.
    setoid_rewrite assoc. setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 3.
    cut(in1 o (@empty unit) === in2).
      intro H1. rewrite H1.
      rewrite assoc. rewrite (@ss_lcopair_eq _ _ _ rw).
      setoid_rewrite assoc. setoid_rewrite <- assoc at 2.
      transitivity (((update y o constant 7) o id) o
      ((update x o constant 0) o (update y o constant 20))).
      repeat setoid_rewrite <- assoc. setoid_rewrite assoc. apply swrepl. reflexivity.
      setoid_rewrite assoc at 1. apply (@pswsubs _ _ _ rw).
      apply eax1. unfold pure_id. 
      split. decorate. reflexivity. rewrite ids. setoid_rewrite <- assoc at 3.
      rewrite CUU. setoid_rewrite assoc at 1.
      rewrite IUU.
      rewrite CUU. reflexivity.
      exact H. auto. decorate.
      repeat apply is_comp. unfold lpi. 
    (*1st cut*)
    setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate].
    decorate.
    easy. decorate. easy.
 Qed.

End Make.

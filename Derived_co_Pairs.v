(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Axioms.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
  Module Export Derived_PairsExp := Axioms.Make(M). 

(** PAIRS **)
 
 Definition ppermut {X Y}: term (X*Y) (Y*X) := pair pi2 pi1.
 Definition rpair {X Y Z} (f1: term Y X) (f2: term Z X): term (Y*Z) X := ppermut o pair f2 f1.

 Lemma fst_rpair_eq: forall A B1 B2 (f1: term B1 A) (f2: term B2 A),
 RO epure f2 -> RO epure f1 -> pi1 o rpair f1 f2 === f1.
 Proof.
    intros A B1 B2 f1 f2 H1 H2. unfold rpair, ppermut. rewrite assoc.
    cut(pi1 o pair pi2 pi1 === (@pi2 B2 B1)).
      intro H0. rewrite H0. apply snd_lpair_eq; decorate.
    (*1st cut*)
    apply fst_lpair_eq; decorate.
 Qed.

 Lemma snd_rpair_eq: forall A B1 B2 (f1: term B1 A) (f2: term B2 A),
 RO epure f2 -> RO epure f1 -> pi2 o rpair f1 f2 === f2.
 Proof.
    intros A B1 B2 f1 f2 H1 H2. unfold rpair, ppermut. rewrite assoc.
    cut(pi2 o pair pi2 pi1 === (@pi1 B2 B1)).
      intro H0. rewrite H0. apply fst_lpair_eq; decorate.
    (* 1st cut *)
    apply snd_lpair_eq; decorate.
 Qed.

 Lemma ss_lpair_u: forall A B1 B2 (f g: term (B1*B2) A),
 (pi1 o f ~== pi1 o g) -> (pi2 o f === pi2 o g) -> f === g.
 Proof.
    intros A B1 B2 f g H1 H2. apply effect.
    cut ((@forget B2) o (@pi2 B1 B2) === (@forget (B1 * B2))).
      intro H0. rewrite <- H0. setoid_rewrite <- assoc.
      apply replsubs; [reflexivity| exact H2].
    (*1st cut*)
    apply ss_unit; edecorate.
    apply lpair_ueq. exact H1. apply sstows. exact H2.
 Qed.

 Lemma ss_rpair_u: forall A B1 B2 (f g: term (B1*B2) A),
 (pi1 o f === pi1 o g) -> (pi2 o f ~== pi2 o g) -> f === g.
 Proof.
    intros A B1 B2 f g H1 H2. apply effect.
    cut ((@forget B1) o (@pi1 B1 B2) === (@forget (B1 * B2))).
      intro H0. rewrite <- H0. setoid_rewrite <- assoc.
      apply replsubs; [reflexivity| exact H1].
    (*1st cut*)
    apply ss_unit; edecorate.
    apply lpair_ueq.  apply sstows. exact H1. exact H2.
 Qed.


(** COPAIRS **)

 Definition cppermut {X Y} : term (X + Y) (Y + X) := copair in2 in1.
 Definition rcopair {X Y Z} (f1: term X Y) (f2: term X Z) : term X (Y + Z) := copair f2 f1 o (@cppermut Z Y).

 Lemma ss_rcopair_eq: forall A B1 B2 d (f1: term A B1) (f2: term A B2),
 PPG d f2 -> CTC d f1 -> rcopair f1 f2 o in1 === f1.
 Proof.
    intros A B1 B2 d f1 f2 H1 H2. unfold rcopair, cppermut. rewrite <- assoc.
    cut (copair in2 in1 o in1 === (@in2 B2 B1)).
      intro H0. rewrite H0. apply (@ss_lcopair_eq _ _ _ d). exact H1.
    (*1st cut*)
    apply (@swtoss _ _ pure); try edecorate.
    apply (@sw_lcopair_eq _ _ _ pure); edecorate.
 Qed.

 Lemma sw_rcopair_eq: forall A B1 B2 d (f1: term A B1) (f2: term A B2),
 PPG d f2 -> CTC d f1 -> rcopair f1 f2 o in2 ==~ f2.
 Proof.
    intros A B1 B2 d f1 f2 H1 H2. unfold rcopair, cppermut. rewrite <- assoc.
    cut (copair in2 in1 o in2 === (@in1 B2 B1)).
      intro H0. rewrite H0. apply (@sw_lcopair_eq _ _ _ d); induction d; edecorate.
    (*1st cut*)
    apply (@ss_lcopair_eq _ _ _ pure); edecorate.
 Qed.

 Lemma ss_lcopair_u: forall A B1 B2 (f g: term A (B1 + B2)),
 (f o in1 ==~ g o in1) -> (f o in2 === g o in2) -> f === g.
 Proof.
    intros A B1 B2 f g H1 H2. apply eeffect.
    cut ((@in2 B1 B2) o (@empty B2) === (@empty (B1 + B2))).
      intro H0. rewrite <- H0. setoid_rewrite assoc.
      apply replsubs; [exact H2 | reflexivity].
    (*1st cut*)
    apply ss_empty; edecorate.
    apply lcopair_ueq. exact H1. apply sstosw. exact H2.
 Qed.

 Lemma ss_rcopair_u: forall A B1 B2 (f g: term A (B1 + B2)),
 (f o in1 === g o in1) -> (f o in2 ==~ g o in2) -> f === g.
 Proof.
    intros A B1 B2 f g H1 H2. apply eeffect.
    cut ((@in1 B1 B2) o (@empty B1) === (@empty (B1 + B2))).
      intro H0. rewrite <- H0. setoid_rewrite assoc.
      apply replsubs; [exact H1 | reflexivity].
    (*1st cut*)
    apply ss_empty; edecorate.
    apply lcopair_ueq. apply sstosw. exact H1. exact H2.
 Qed.

 (* additional lemmas about [pbl] and [copair] *)
 Lemma pbl_true: pbl o constant true === in1.
 Proof.
     unfold pbl, constant, in1, bool_to_two. rewrite <- tcomp.
     unfold compose. apply imp6.
     intros. rewrite x. reflexivity.
 Qed.

 Lemma pbl_false: pbl o constant false === in2.
 Proof. 
     unfold pbl, constant, in1, bool_to_two. rewrite <- tcomp.
     apply imp6. intros. rewrite x. reflexivity.
 Qed.

 Lemma copair_true: forall k A f g, PPG k f -> PPG k g ->  @copair _ _ A f g o (pbl o constant true) === f.
 Proof. intros k A f g H0 H1. rewrite pbl_true.
          apply (@swtoss _ _ k). induction k; decorate. exact H0. 
          apply (@sw_lcopair_eq _ _ _ k); edecorate.
 Qed.

 Lemma copair_false: forall k A f g, PPG k f -> PPG k g ->  @copair _ _ A f g o (pbl o constant false) === g.
 Proof. intros k A f g H0 H1. rewrite pbl_false. apply (@ss_lcopair_eq _ _ _ k); edecorate. Qed.


(* -------------------- End of Derived (co)Pair Projections -------------------- *)


End Make.




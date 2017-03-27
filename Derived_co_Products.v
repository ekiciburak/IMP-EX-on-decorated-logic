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
Require Memory Terms Decorations Axioms Derived_co_Pairs.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_co_ProductsExp := Derived_co_Pairs.Make(M). 

 (**PRODUCTS**)

 Definition lprod {X Y X' Y'} (f: term X X') (g: term Y Y') := pair (f o pi1) (g o pi2).
 Definition rprod {X Y X' Y'} (f: term X X') (g: term Y Y') := ppermut o pair (g o pi2) (f o pi1).

 Lemma fst_lprod_eq: forall A1 A2 B1 B2 (f: term B1 A1) (g: term B2 A2),
 RO epure f -> RO epure g -> pi1 o (lprod f g) === f o pi1.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply fst_lpair_eq; decorate. Qed.

 Lemma snd_lprod_eq: forall A1 A2 B1 B2 (f: term B1 A1) (g: term B2 A2),
 RO epure f -> RO epure g -> pi2 o (lprod f g) === g o pi2.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply snd_lpair_eq; decorate. Qed.

 Lemma fst_rprod_eq: forall A1 A2 B1 B2 (f: term B1 A1) (g: term B2 A2),
 RO epure g -> RO epure f -> pi1 o (rprod f g) === f o pi1.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply fst_rpair_eq; decorate. Qed.

 Lemma snd_rprod_eq: forall A1 A2 B1 B2 (f: term B1 A1) (g: term B2 A2),
 RO epure g -> RO epure f -> pi2 o (rprod f g) === g o pi2.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply snd_rpair_eq; decorate. Qed.

(*product unicity*)

 Lemma ss_lprod_u: forall A1 A2 B1 B2 (f g: term (B1*B2) (A1*A2)),
 (pi1 o f ~== pi1 o g) -> (pi2 o f === pi2 o g) -> f === g.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply ss_lpair_u; [exact H1| exact H2]. Qed.

 Lemma ss_rprod_u: forall A1 A2 B1 B2 (f g: term (B1*B2) (A1*A2)),
 (pi1 o f === pi1 o g) -> (pi2 o f ~== pi2 o g) -> f === g.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply ss_rpair_u; [exact H1| exact H2]. Qed.

(**COPRODUCTS**)

 Definition lcoprod {X1 Y1 X2 Y2} (f: term X1 X2) (g: term Y1 Y2) := copair (in1 o f) (in2 o g).
 Definition rcoprod {X1 Y1 X2 Y2} (f: term X1 X2) (g: term Y1 Y2) := rcopair (in1 o f) (in2 o g).

 Lemma sw_lcoprod_eq: forall A1 A2 B1 B2 d (f: term B1 A1) (g: term A2 B2),
 PPG d f -> CTC d g -> (lcoprod f g) o in1 ==~ in1 o f.
 Proof. intros A1 A2 B1 B2 d f g H1 H2. apply (@sw_lcopair_eq _ _ _ d); induction d; edecorate. Qed.
 
 Lemma ss_lcoprod_eq: forall A1 A2 B1 B2 d (f: term B1 A1) (g: term A2 B2),
 PPG d f -> CTC d g -> (lcoprod f g) o in2 === in2 o g.
 Proof. intros A1 A2 B1 B2 d f g H1 H2. apply (@ss_lcopair_eq _ _ _ d); induction d; edecorate. Qed.

 Lemma ss_rcoprod_eq: forall A1 A2 B1 B2 d (f: term B1 A1) (g: term A2 B2),
 PPG d g -> CTC d f -> (rcoprod f g) o in1 === in1 o f.
 Proof. intros A1 A2 B1 B2 d f g H1 H2. apply (@ss_rcopair_eq _ _ _ d); induction d; edecorate. Qed.

 Lemma sw_rcoprod_eq: forall A1 A2 B1 B2 d (f: term B1 A1) (g: term A2 B2),
 PPG d g -> CTC d f -> (rcoprod f g) o in2 ==~ in2 o g.
 Proof. intros A1 A2 B1 B2 d f g H1 H2. apply (@sw_rcopair_eq _ _ _ d); induction d; edecorate. Qed.

(*coproduct unicity*)

 Lemma ss_lcoprod_u: forall A1 A2 B1 B2 (f g: term (A1 + A2) (B1 + B2)),
 (f o in1 ==~ g o in1) -> (f o in2 === g o in2) -> f === g.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply ss_lcopair_u;[exact H1| exact H2]. Qed.

 Lemma ss_rcoprod_u: forall A1 A2 B1 B2 (f g: term (A1 + A2) (B1 + B2)),
 (f o in1 === g o in1) -> (f o in2 ==~ g o in2) -> f === g.
 Proof. intros A1 A2 B1 B2 f g H1 H2. apply ss_rcopair_u;[exact H1| exact H2]. Qed.

End Make.


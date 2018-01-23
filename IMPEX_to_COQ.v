(**************************************************************************)
(*  This is part of IMP-STATES-EXCEPTIONS, it is distributed under the    *)
(*       terms  of the GNU Lesser General Public License version 3        *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Axioms Derived_co_Pairs
        Derived_co_Products Proofs Functions.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Unset Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export IMPEX_to_COQExp := Functions.Make(M).

 Inductive aExp : Type :=
    | aconst: Z -> aExp
    | var   : Loc -> aExp
    | plus  : aExp -> aExp -> aExp
    | subtr : aExp -> aExp -> aExp
    | mult  : aExp -> aExp -> aExp
with bExp : Type :=
    | bconst: bool -> bExp
    | ttrue : bExp
    | ffalse: bExp
    | eq    : aExp -> aExp -> bExp
    | neq   : aExp -> aExp -> bExp
    | gt    : aExp -> aExp -> bExp
    | lt    : aExp -> aExp -> bExp
    | ge    : aExp -> aExp -> bExp
    | le    : aExp -> aExp -> bExp
    | and   : bExp -> bExp -> bExp
    | or    : bExp -> bExp -> bExp
    | neg   : bExp -> bExp.

 Fixpoint daExp (e: aExp): term Z unit :=
  match e with
    | aconst n      => constant n
    | var x         => lookup x
    | plus a1 a2    => tpure add o pair (daExp a1) (daExp a2)
    | subtr a1 a2   => tpure subt o pair (daExp a1) (daExp a2)
    | mult a1 a2    => tpure mlt o pair (daExp a1) (daExp a2)
  end.

Definition state := Loc -> Z.

Definition empty_state : state := fun _ => 0.

Fixpoint aeval (st : state) (e : aExp) : Z :=
  match e with
    | aconst n => n
    | var X => st X 
    | plus a1 a2 => (aeval st a1) + (aeval st a2)
    | subtr a1 a2  => (aeval st a1) - (aeval st a2)
    | mult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

 Fixpoint dbExp (e: bExp): term bool unit :=
  match e with
    | bconst n      => constant n
    | ttrue         => constant true
    | ffalse        => constant false
    | eq a1 a2      => tpure chkeq o pair (daExp a1) (daExp a2)
    | neq a1 a2     => tpure chkneq o pair (daExp a1) (daExp a2)
    | gt a1 a2      => tpure chkgt o pair (daExp a1) (daExp a2)
    | lt a1 a2      => tpure chklt o pair (daExp a1) (daExp a2)
    | ge a1 a2      => tpure chkge o pair (daExp a1) (daExp a2)
    | le a1 a2      => tpure chkle o pair (daExp a1) (daExp a2)
    | and b1 b2     => tpure andB o pair (dbExp b1) (dbExp b2)
    | or b1 b2      => tpure orB o pair (dbExp b1) (dbExp b2)
    | neg b         => tpure notB o (dbExp b)
  end.

Fixpoint beval (st : state) (e : bExp) : bool :=
  match e with
    | bconst n   => n
    | ttrue      => true
    | ffalse     => false
    | eq a1 a2   => Zeq_bool (aeval st a1) (aeval st a2)
    | neq a1 a2  => negb (Zeq_bool (aeval st a1) (aeval st a2))
    | gt a1 a2   => Zgt_bool (aeval st a1) (aeval st a2)
    | lt a1 a2   => Zlt_bool (aeval st a1) (aeval st a2)
    | le a1 a2   => Zle_bool (aeval st a1) (aeval st a2)
    | ge a1 a2   => Zge_bool (aeval st a1) (aeval st a2)
    | and b1 b2  => andb (beval st b1) (beval st b2)
    | or b1 b2   => orb (beval st b1) (beval st b2)
    | neg b1     => negb (beval st b1)
  end.

 Inductive Cmd  : Type :=
    | skip      : Cmd
    | sequence  : Cmd   -> Cmd  -> Cmd
    | assign    : Loc   -> aExp -> Cmd 
    | cond      : bExp  -> Cmd  -> Cmd -> Cmd
    | while     : bExp  -> Cmd  -> Cmd
    | THROW     : EName -> Cmd
    | TRY_CATCH : EName -> Cmd  -> Cmd -> Cmd.

Definition Uupdate (st : state) (X: Loc) (n : Z): state :=
  fun X' => if Zeq_bool (loc X) (loc X') then n else st X'.

Theorem update_eq : forall n X st, (Uupdate st X n) X = n.
Proof. intros.
       unfold Uupdate, Zeq_bool.
       now rewrite Z.compare_refl.
Qed.

Inductive ceval : Cmd -> state -> state -> Prop :=
  | E_Skip: forall st, ceval skip st st
  | E_Ass : forall st a1 n X, aeval st a1 = n -> ceval (assign X a1) st (Uupdate st X n)
  | E_Seq : forall c1 c2 st st' st'', ceval c1 st st' -> ceval c2 st' st'' -> ceval (sequence c1 c2) st st''
  | E_IfTrue : forall st st' b1 c1 c2, beval st b1 = true  -> ceval c1 st st' -> ceval (cond b1 c1 c2) st st'
  | E_IfFalse: forall st st' b1 c1 c2, beval st b1 = false -> ceval c2 st st' -> ceval (cond b1 c1 c2) st st'
  | E_WhileEnd : forall b1 st c1, beval st b1 = false -> ceval (while b1 c1) st st
  | E_WhileLoop : forall st st' st'' b1 c1, beval st b1 = true -> ceval c1 st st' ->
                                            ceval (while b1 c1) st' st'' -> ceval (while b1 c1) st st''
  | E_Throw: forall e st, ceval (THROW e) st st
  | E_TC: forall e c1 c2 st , ceval (TRY_CATCH e c1 c2) st st.

 Fixpoint dCmd (c: Cmd): (term unit unit) :=
  match c with
    | skip              => (@id unit)
    | sequence c0 c1    => (dCmd c1) o (dCmd c0)
    | assign j e0       => (update j) o (daExp e0)
    | cond b c2 c3      => copair (dCmd c2) (dCmd c3) o (pbl o (dbExp b))
    | while b c4        => (copair (lpi (pbl o (dbExp b)) (dCmd c4) o (dCmd c4)) (@id unit)) o (pbl o (dbExp b))
    | THROW e           => (throw unit e)
    | TRY_CATCH e c1 c2 => (try_catch e (dCmd c1) (dCmd c2))
  end.

Theorem equiv: forall c1 c2 st st', (dCmd c1 === dCmd c2) -> ceval c1 st st' -> ceval c2 st st'.
Proof. Admitted.
       

 Notation "j '::=' e0"                            := (assign j e0) (at level 60).
 Notation "c1 ';;' c2"                            := (sequence c1 c2) (at level 60).
 Notation "'SKIP'"                                := (skip) (at level 60).
 Notation "'IFB' b 'THEN' t1 'ELSE' t2 'ENDIF'"   := (cond b t1 t2) (at level 60).
 Notation "'WHILE' b 'DO' c 'ENDWHILE'"           := (while b c) (at level 60).
 Notation "'THROW' en"                            := (THROW en) (at level 60).
 Notation "'TRY' s0 'CATCH' e '=>' s1"            := (TRY_CATCH e s0 s1) (at level 60).

 Notation " x '+++' y"                            := (plus x y)(at level 60).
 Notation " x '---' y"                            := (subtr x y) (at level 60).
 Notation " x '***' y"                            := (mult x y) (at level 59).
 Notation " x '>>' y"                             := (gt x y) (at level 60).
 Notation " x '<<' y"                             := (lt x y) (at level 60).
 Notation " x '>>=' y"                            := (ge x y) (at level 60).
 Notation " x '<<=' y"                            := (le x y) (at level 60).
 Notation " x '?==' y"                            := (eq x y) (at level 60).
 Notation " x '?!==' y"                           := (neq x y) (at level 60).
 Notation " x '?&' y"                             := (and x y) (at level 60).
 Notation " x '?|' y"                             := (or x y) (at level 60).
 Notation " '-~' x"                               := (neg x) (at level 60). 
 Notation "'{{' c '}}'"                           := (dCmd c) (at level 62).
 Notation "'``' c '``'"                           := (daExp c) (at level 62).

Lemma lm2: forall (x: Loc),
	let c1 := (x ::= (aconst 2) ;;
	  WHILE ((var x) << (aconst 11))
	    DO (x ::= ((var x) +++ (aconst 4)))
	  ENDWHILE) in
   ceval c1 empty_state (Uupdate empty_state x 14).
Proof. intros.
       unfold c1.
       apply E_Seq with (Uupdate empty_state x 2).
       apply E_Ass. now cbn.
       apply E_WhileLoop with (Uupdate (Uupdate empty_state x 2) x 6).
       cbn. rewrite update_eq. easy.
       apply E_Ass.
       cbn. now rewrite update_eq.
       apply E_WhileLoop with (Uupdate (Uupdate (Uupdate empty_state x 2) x 6) x 10).
       cbn. rewrite update_eq. easy.
       apply E_Ass.
       cbn. now rewrite update_eq.
       apply E_WhileLoop with (Uupdate (Uupdate (Uupdate (Uupdate empty_state x 2) x 6) x 10) x 14).
       cbn. now rewrite update_eq.
       apply E_Ass.
       cbn. now rewrite update_eq.
       specialize (E_WhileEnd (var x << aconst 11) (Uupdate empty_state x 14) (x ::= (var x +++ aconst 4)) ); intros.
       assert ((Uupdate (Uupdate (Uupdate (Uupdate empty_state x 2) x 6) x 10) x 14) = (Uupdate empty_state x 14)).
       { unfold Uupdate. extensionality y.
         case_eq (Zeq_bool (loc x) (loc y)); intros; easy.
       }
       rewrite H0.
       apply H.
       cbn. rewrite update_eq. easy.
Qed.


(* -------------------- End of IMP to COQ conversion -------------------- *)

End Make.



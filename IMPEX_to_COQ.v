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
        Derived_co_Products Proofs Functions.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
  Module Export IMPEX_to_COQExp := Functions.Make(M).

 Inductive Exp : Type -> Type :=
    | const : forall A, A          -> Exp A
    | loc   : Loc                  -> Exp Z
    | apply : forall A B, (A -> B) -> Exp A -> Exp B
    | pExp  : forall A B, Exp A    -> Exp B -> Exp (A * B).

 Fixpoint dExp A (e: Exp A): term A unit :=
  match e with
    | const Z n     => constant n
    | loc x         => lookup x
    | apply _ _ f x => tpure f o (dExp x)
    | pExp _ _  x y => pair (dExp x) (dExp y)
  end.

 Inductive Cmd  : Type :=
    | skip      : Cmd
    | sequence  : Cmd      -> Cmd   -> Cmd
    | assign    : Loc      -> Exp Z -> Cmd 
    | cond      : Exp bool -> Cmd   -> Cmd -> Cmd
    | while     : Exp bool -> Cmd   -> Cmd
    | THROW     : EName    -> Cmd
    | TRY_CATCH : EName    -> Cmd   -> Cmd -> Cmd.

 Fixpoint dCmd (c: Cmd): (term unit unit) :=
  match c with
    | skip              => (@id unit)
    | sequence c0 c1    => (dCmd c1) o (dCmd c0)
    | assign j e0       => (update j) o (dExp e0)
    | cond b c2 c3      => copair (dCmd c2) (dCmd c3) o (pbl o (dExp b))
    | while b c4        => (copair (lpi (pbl o (dExp b)) (dCmd c4) o (dCmd c4)) (@id unit)) o (pbl o (dExp b))
    | THROW e           => (throw unit e)
    | TRY_CATCH e c1 c2 => (@try_catch _ _ e (dCmd c1) (dCmd c2))
  end.


 (*     | trycatch t1 c5 c6 => (@TRY_CATCH _ _ t1 (dCmd c5) (dCmd c6)) *)

 Notation "j '::=' e0"                            := (assign j e0) (at level 60).
 Notation "c1 ';;' c2"                            := (sequence c1 c2) (at level 60).
 Notation "'SKIP'"                                := (skip) (at level 60).
 Notation "'IFB' b 'THEN' t1 'ELSE' t2 'ENDIF'"   := (cond b t1 t2) (at level 60).
 Notation "'WHILE' b 'DO' c 'ENDWHILE'"           := (while b c) (at level 60).
 Notation " x '+++' y"                            := (apply add (pExp x y)) (at level 60).
 Notation " x '---' y"                            := (apply subs (pExp x y)) (at level 60).
 Notation " x '***' y"                            := (apply mlt (pExp x y)) (at level 59).
 Notation " x '///' y"                            := (apply div (pExp x y)) (at level 59).
 Notation " x '?%' y"                             := (apply modulo (pExp x y)) (at level 60).
 Notation " x '>>' y"                             := (apply chkgt (pExp x y)) (at level 60).
 Notation " x '>>=' y"                            := (apply chkge (pExp x y)) (at level 60).
 Notation " x '<<' y"                             := (apply chklt (pExp x y)) (at level 60).
 Notation " x '<<=' y"                            := (apply chkle (pExp x y)) (at level 60).
 Notation " x '?==' y"                            := (apply chkeq (pExp x y)) (at level 60).
 Notation " x '?!==' y"                           := (apply chkneq (pExp x y)) (at level 60).
 Notation " x '?&' y"                             := (apply ve (pExp x y)) (at level 60).
 Notation " x '?|' y"                             := (apply yada (pExp x y)) (at level 60). 
 Notation "'THROW' en"                            := (THROW en) (at level 60).
 Notation "'TRY' s0 'CATCH' e '=>' s1"            := (TRY_CATCH e s0 s1) (at level 60).
 Notation "'{{' c '}}'"                           := (dCmd c) (at level 62).
 Notation "'``' c '``'"                           := (dExp c) (at level 62).

(* -------------------- End of IMP to COQ conversion -------------------- *)

End Make.



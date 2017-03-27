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

Unset Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export IMPEX_to_COQExp := Functions.Make(M).

 Inductive Exp : Type -> Type :=
    | const : forall A, A -> Exp A
    | var   : Loc -> Exp Z
    | plus  : Exp Z -> Exp Z -> Exp Z
    | subtr : Exp Z -> Exp Z -> Exp Z
    | mult  : Exp Z -> Exp Z -> Exp Z
    | ttrue : Exp bool
    | ffalse: Exp bool
    | eq    : Exp Z -> Exp Z -> Exp bool
    | neq   : Exp Z -> Exp Z -> Exp bool
    | gt    : Exp Z -> Exp Z -> Exp bool
    | lt    : Exp Z -> Exp Z -> Exp bool
    | ge    : Exp Z -> Exp Z -> Exp bool
    | le    : Exp Z -> Exp Z -> Exp bool
    | and   : Exp bool -> Exp bool -> Exp bool
    | or    : Exp bool -> Exp bool -> Exp bool
    | neg   : Exp bool -> Exp bool.

 Fixpoint dExp A (e: Exp A): term A unit :=
  match e with
    | const Z n     => constant n
    | var x         => lookup x
    | plus a1 a2    => tpure add o pair (dExp Z a1) (dExp Z a2)
    | subtr a1 a2   => tpure subt o pair (dExp Z a1) (dExp Z a2)
    | mult a1 a2    => tpure mlt o pair (dExp Z a1) (dExp Z a2)
    | ttrue         => constant true
    | ffalse        => constant false
    | eq a1 a2      => tpure chkeq o pair (dExp Z a1) (dExp Z a2)
    | neq a1 a2     => tpure chkneq o pair (dExp Z a1) (dExp Z a2)
    | gt a1 a2      => tpure chkgt o pair (dExp Z a1) (dExp Z a2)
    | lt a1 a2      => tpure chklt o pair (dExp Z a1) (dExp Z a2)
    | ge a1 a2      => tpure chkge o pair (dExp Z a1) (dExp Z a2)
    | le a1 a2      => tpure chkle o pair (dExp Z a1) (dExp Z a2)
    | and b1 b2     => tpure andB o pair (dExp bool b1) (dExp bool b2)
    | or b1 b2      => tpure orB o pair (dExp bool b1) (dExp bool b2)
    | neg b         => tpure notB o (dExp bool b)
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
    | assign j e0       => (update j) o (dExp Z e0)
    | cond b c2 c3      => copair (dCmd c2) (dCmd c3) o (pbl o (dExp bool b))
    | while b c4        => (copair (lpi (pbl o (dExp bool b)) (dCmd c4) o (dCmd c4)) (@id unit)) o (pbl o (dExp bool b))
    | THROW e           => (throw unit e)
    | TRY_CATCH e c1 c2 => (try_catch e (dCmd c1) (dCmd c2))
  end.

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
 Notation "'``' c '``'"                           := (dExp c) (at level 62).

(* -------------------- End of IMP to COQ conversion -------------------- *)

End Make.



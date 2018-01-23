(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).

 Inductive term: Type -> Type -> Type :=
  | tpure      : forall {X Y: Type}, (X -> Y) -> term Y X
  | comp       : forall {X Y Z: Type}, term X Y -> term Y Z -> term X Z
  | pair       : forall {X Y Z: Type}, term X Z -> term Y Z -> term (X*Y) Z
  | copair     : forall {X Y Z}, term Z X -> term Z Y -> term Z (X+Y) 
  | downcast   : forall {X Y} (f: term X Y), term X Y 
  | lookup     : forall i:Loc, term Z unit
  | update     : forall i:Loc, term unit Z
  | tag        : forall e: EName, term Empty_set unit	
  | untag      : forall e: EName, term unit Empty_set.

 Infix "o" := comp (at level 60).


 Definition id  {X: Type}            : term X X     := tpure id.
 Definition pi1 {X Y: Type}          : term X (X*Y) := tpure fst.
 Definition pi2 {X Y: Type}          : term Y (X*Y) := tpure snd.
 Definition forget {X}               : term unit X  := tpure (fun _ => tt).
 Definition constant {X: Type} (v: X): term X unit  := tpure (fun _ => v).
 Definition emptyfun (X: Type) (e: Empty_set) : X := match e with end.
 Definition empty X: term X Empty_set := tpure (emptyfun X).
 Definition in1 {X Y}    : term (X+Y) X     := tpure inl.
 Definition in2 {X Y}    : term (X+Y) Y     := tpure inr.

Definition throw (X: Type) (e: EName): term X unit := (empty X) o tag e.
Definition try_catch (X Y: Type) (e: EName) (f: term Y X) (g: term Y unit) := downcast(copair (@id Y) (g o untag e) o in1 o f).

(**IMP terms: additional**)

 Definition lpi (b: term (unit+unit) unit) (f: term unit unit) : term unit unit  
    := tpure(fun tt => tt). 

 Definition bool_to_two (b: bool): unit + unit :=
    match b with
       | false => inr tt
       | true  => inl tt
    end.

 Definition pbl: term (unit + unit) bool := tpure bool_to_two.

End Make.


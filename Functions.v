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
Require Memory Terms Decorations Axioms Derived_co_Pairs Derived_co_Products Proofs.
Set Implicit Arguments.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
Require Setoid.

Module Make(Import M: Memory.T).
  Module Export FunctionsExp := Proofs.Make(M).

 Definition modulo (p: Z * Z) := 
    match p with
      | (x, y) => x mod y
    end.

 Definition add (p: Z * Z) := 
    match p with
      | (x, y) => x + y
    end.

 Definition subt (p: Z * Z) := 
    match p with
      | (x, y) => x - y
    end.

 Definition mlt (p: Z * Z) := 
    match p with
      | (x, y) => x * y
    end.

 Definition div (p: Z * Z) := 
    match p with
      | (x, y) => x / y
    end.

 Definition chkgt (p: Z * Z) : bool := 
    match p with
      | (a1, a2) => match (a1 ?= a2)%Z with 
                      | Gt => true
                      | _  => false
                    end
    end.

 Definition chkge (p: Z * Z) : bool := 
     match p with
       | (a1, a2) => match (a1 ?= a2)%Z with 
                       | Lt => false
                       | _  => true
                     end
     end.

 Definition chklt (p: Z * Z) : bool := 
    match p with
      | (a1, a2) => match (a1 ?= a2)%Z with 
                      | Lt => true
                      | _  => false
                    end
    end.

 Definition chkle (p: Z * Z) : bool :=
    match p with
      | (a1, a2) => match (a1 ?= a2)%Z with 
                      | Gt => false
                      | _  => true
                    end
    end.

 Definition chkeq (p: Z * Z) : bool := 
    match p with
      | (a1, a2) => match (a1 ?= a2)%Z with 
                      | Eq => true
                      | _  => false
                    end
    end.

 Definition chkneq (p: Z * Z) : bool := 
    match p with
      | (a1, a2) => match (a1 ?= a2)%Z with 
                      | Eq => false
                      | _  => true
                    end
    end.

 Definition andB (p: bool * bool): bool := 
    match p with
      | (x, y) => match (x && y) with 
                    | false => false
                    | true  => true
                  end
    end.

 Definition orB (p: bool * bool): bool := 
    match p with
      | (x, y) => match (x || y) with 
                    | false => false
                    | true  => true
                  end
    end.

 Definition notB (b: bool): bool := if b then false else true.

 Definition bool_to_prop (b: bool): Prop :=
     match b with
       | false => False
       | true  => True
    end.


End Make.
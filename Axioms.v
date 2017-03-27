(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2015: Jean-Guillaume Dumas, Dominique Duval            *)
(*             Burak Ekici, Damien Pous.                                  *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
Module Export AxiomsExp := Decorations.Make(M).

 Definition pure_id k A B (x y: term A B) := is (k, epure) x /\ x=y.
 Definition idem A B (x y: term A B) := x=y.

 Coercion is_true: bool >-> Sortclass.
 
 Reserved Notation "x === y" (at level 80).
 Reserved Notation "x ~== y" (at level 80).
 Reserved Notation "x ==~ y" (at level 80).
 Reserved Notation "x ~~ y"  (at level 80). 

 Inductive ss: forall X Y, relation (term X Y) :=
  | ssrefl: forall X Y (f: term X Y), f === f
  | sssym: forall X Y, Symmetric (@ss X Y)
  | sstrans: forall X Y, Transitive (@ss X Y)
  | assoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T), f o (g o h) === (f o g) o h
  | ids: forall X Y (f: term X Y), f o id === f
  | idt: forall X Y (f: term X Y), id o f === f
  | replsubs: forall X Y Z, Proper (@ss X Y ==> @ss Y Z ==> @ss X Z) comp
  | replsubsp: forall X Y Z, Proper (@ss X Z ==> @ss Y Z ==> @ss (X*Y) Z) pair
  | replsubscp: forall X Y Z, Proper (@ss Z X ==> @ss Z Y ==> @ss Z (X+Y)) copair
  | wstoss: forall X Y k (f g: term X Y), RO k f -> RO k g -> f ~== g -> f === g
  | effect: forall X Y (f g: term Y X), forget o f === forget o g -> f ~== g -> f === g (* effect measure - Dumas et al.'12 *)
  | local_global: forall X (f g: term unit X), (forall i: Loc, lookup i o f ~== lookup i o g) -> f === g
  | fst_lpair_eq: forall X Y' Y (f1: term Y X) (f2: term Y' X), RO epure f1 -> RO epure f2 -> pi1 o pair f1 f2 === f1
  | snd_lpair_eq: forall X Y' Y (f1: term Y X) (f2: term Y' X), RO epure f1 -> RO epure f2 -> pi2 o pair f1 f2 === f2
  | swtoss: forall X Y k (f g: term X Y), PPG k f -> PPG k g -> f ==~ g -> f === g
  | eeffect: forall X Y (f g: term Y X), (f o (empty X) === g o (empty X)) -> f ==~ g -> f === g (* dual effect measure - Dumas et al.'14 *)
  | elocal_global: forall X (f g: term X Empty_set), (forall t: EName, f o tag t ==~ g o tag t) -> f === g (* dual to eq3 *)
  | ss_lcopair_eq: forall X X' Y k (f1: term Y X) (f2: term Y X'), PPG k f1 -> (copair f1 f2) o in2 === f2
 (* | tcomp: forall X Y Z (f: Y -> Z) (g: X -> Y), tpure f o tpure g  === tpure (fun x => f (g x)) *)
       (*IMP Assumptions*)
  | imp_loopiter: forall (b: term (unit+unit) unit) (f : term unit unit), lpi b f === (copair ((lpi b f) o f) id) o b 
  | imp1: forall (p q: Z) (f: Z*Z -> Z), tpure f o (pair (@constant Z p) (@constant Z q)) === (constant (f(p,q)))
  | imp2: forall (p q: Z) (f: Z*Z -> bool), f(p, q) = false -> pbl  o (tpure f o (pair (@constant Z p) (@constant Z q))) === in2
  | imp3: forall (p q: Z) (f: Z*Z -> bool), f(p, q) -> pbl  o (tpure f o (pair (@constant Z p) (@constant Z q))) === in1
  | imp4: forall (p q: bool) (f: bool*bool -> bool), f(p, q) = false -> pbl o (tpure f o (pair (@constant bool p) (@constant bool q))) === in2
  | imp5: forall (p q: bool) (f: bool*bool -> bool), f(p, q) -> pbl o (tpure f o (pair (@constant bool p) (@constant bool q))) === in1
  | imp6: forall X Y (f g: Y -> X), (forall x, f x = g x) -> tpure f === tpure g
  | tcomp: forall X Y Z (f: Z -> Y) (g: Y -> X), tpure (compose g f) === tpure g o tpure f
       (*\IMP Assumptions*)
 with ws: forall X Y, relation (term X Y) := 
  | wssym: forall X Y, Symmetric (@ws X Y)
  | wstrans: forall X Y, Transitive (@ws X Y)
  | wsassoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T), f o (g o h) ~== (f o g) o h
  | wssubs: forall A B C, Proper (@ws C B ==> @idem B A ==> @ws C A) comp
  | pwsrepl: forall A B C k (g: term C B), (PURE k g) -> Proper (@ws B A ==> @ws C A) (comp g)
  | wwtows: forall X Y k (f g: term X Y), PPG k f -> PPG k g -> f ~~ g -> f ~== g
  | ws_unit: forall X (f g: term unit X), f ~== g
  | ax1: forall i, lookup i o update i ~== (@id Z)
  | ax2: forall i j, i<>j -> lookup j o update i ~== lookup j o (@forget Z)
  | sstows: forall  X Y (f g: term X Y), f === g -> f ~== g
  | lpair_ueq: forall X Y' Y (f1: term (Y*Y') X) (f2: term (Y*Y') X), (pi1 o f1 ~== pi1 o f2) -> (pi2 o f1 ~== pi2 o f2) -> f1 ~== f2
 with sw: forall X Y, relation (term X Y) := 
  | swsym: forall X Y, Symmetric (@sw X Y)
  | swtrans: forall X Y, Transitive (@sw X Y)
  | swassoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T), f o (g o h) ==~ (f o g) o h
  | swrepl : forall A B C, Proper (@idem C B ==> @sw B A ==> @sw C A) comp
  | pswsubs : forall A B C k, Proper (@sw C B ==> @pure_id k B A ==> @sw C A) comp
  | wwtosw: forall X Y k (f g: term X Y), RO k f -> RO k g -> f ~~ g -> f ==~ g
  | sw_empty: forall X (f g: term X Empty_set), f ==~ g	
  | eax1: forall e: EName, untag e o tag e ==~ (@id unit)
  | eax2: forall (e1 e2: EName), e1 <> e2 -> untag e2 o tag e1 ==~ (empty unit) o tag e1
  | sstosw: forall  X Y (f g: term X Y), f === g -> f ==~ g
  | sw_downcast: forall X Y (f: term X Y), f ==~ (@downcast X Y f)
  | sw_lcopair_eq: forall X X' Y k (f1: term Y X) (f2: term Y X'), PPG k f1 -> (copair f1 f2) o in1 ==~ f1
  | lcopair_ueq: forall  X X' Y (f g: term Y (X+X')), (f o in1 ==~ g o in1) -> (f o in2 ==~ g o in2) -> f ==~ g
 with ww: forall X Y, relation (term X Y) :=
  | wwsym: forall X Y, Symmetric (@ww X Y)
  | wwtrans: forall X Y, Transitive (@ww X Y)
  | wstoww: forall X Y (f g: term X Y), f ~== g -> f ~~ g
  | swtoww: forall X Y (f g: term X Y), f ==~ g -> f ~~ g
  | sstoww: forall X Y (f g: term X Y), f === g -> f ~~ g
 where "x === y" := (ss x y)
   and "x ~== y" := (ws x y)
   and "x ==~ y" := (sw x y)
   and "x ~~ y" := (ww x y).

 Instance Eqss: forall X Y, Equivalence (@ss X Y).
 Proof. constructor; intro. apply ssrefl. apply sssym. apply sstrans. Qed.

 Instance Eqws: forall X Y, Equivalence (@ws X Y).
 Proof. constructor; intro. apply sstows. apply ssrefl. apply wssym. apply wstrans. Qed.

 Instance Eqsw: forall X Y, Equivalence (@sw X Y).
 Proof. constructor; intro. apply sstosw. apply ssrefl. apply swsym. apply swtrans. Qed.

 Instance Eqww: forall X Y, Equivalence (@ww X Y).
 Proof. constructor; intro. apply sstoww. apply ssrefl. apply wwsym. apply wwtrans. Qed.

 Instance Sub_ss_ww: forall X Y, subrelation (@ss X Y) (@ww X Y).
 Proof. intros. constructor. apply sstoww. apply sssym. assumption. Qed.

 Instance Sub_ss_sw: forall X Y, subrelation (@ss X Y) (@sw X Y).
 Proof. constructor. apply sstosw. apply sssym. exact H. Qed.  

 Instance Sub_ss_ws: forall X Y, subrelation (@ss X Y) (@ws X Y).
 Proof. constructor. apply sstows. apply sssym. exact H. Qed.  

 Existing Instance wssubs.
 Existing Instance pwsrepl.
 Existing Instance swrepl. 
 Existing Instance pswsubs. 
 Existing Instance replsubs.
 Existing Instance replsubsp.
 Existing Instance replsubscp.

 Lemma ss_unit: forall X (f: term unit X), RO ctc f -> f === forget.
 Proof. intros X f H. apply (@wstoss _ _ ctc). exact H. decorate. apply ws_unit. Qed.

 Lemma ss_empty: forall X (f: term X Empty_set), PPG rw f -> f === (@empty X).
 Proof. intros X f H. apply (@swtoss _ _ rw). exact H. edecorate. apply sw_empty. Qed.

End Make.




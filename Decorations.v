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
Require Memory Terms.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
  Module Export DecorationsExp := Terms.Make(M). 

 Inductive kind  := pure  | ro  | rw.
 Inductive ekind := epure | ppg | ctc.
 
 Inductive is   : ((kind * ekind)%type) -> forall X Y, term X Y -> Prop :=
  | is_tpure    : forall X Y (f: X -> Y), is (pure, epure) (@tpure X Y f)
  | is_comp     : forall k X Y Z (f: term X Y) (g: term Y Z), is k f -> is k g -> is k (f o g)
  | is_pair     : forall X Y Z (f: term X Z) (g: term Y Z), is (ro, epure) f -> is (ro, epure) g -> is (ro, epure) (pair f g)
  | is_copair   : forall k1 k2 X Y Z (f: term Z X) (g: term Z Y), is (k1, ppg) f -> is (k1, k2) f -> is (k1, k2) g -> is (k1, k2) (copair f g)  (* FIXED *)
  | is_downcast : forall X Y (f: term X Y), is (pure, ppg) (@downcast X Y f)	
  | is_lookup   : forall i, is (ro, epure) (lookup i)   
  | is_update   : forall i, is (rw, epure) (update i)
  | is_tag      : forall e, is (pure, ppg) (tag e)   
  | is_untag    : forall e, is (pure, ctc) (untag e)
  | is_pure_ro  : forall X Y k (f: term X Y), is (pure, k) f -> is (ro, k) f
  | is_ro_rw    : forall X Y k (f: term X Y), is (ro, k) f -> is (rw, k) f
  | is_pure_ppg : forall X Y k (f: term X Y), is (k, epure) f -> is (k, ppg) f 
  | is_ppg_ctc  : forall X Y k (f: term X Y), is (k, ppg) f -> is (k, ctc) f.

 Hint Constructors is.

 Ltac decorate :=  solve[
                          repeat (apply is_comp || apply is_pair  || apply is_copair)
                            ||
		                 (apply is_tpure    || apply is_lookup || apply is_update || 
	                          apply is_downcast || apply is_tag    || apply is_untag  || assumption)
			    || 
                                 (apply is_pure_ro)
			    || 
		                 (apply is_ro_rw)
			    ||   
                                 (apply is_pure_ppg)
			    ||   
                                 (apply is_ppg_ctc) 
                        ].

 Ltac edecorate :=  solve[
                          repeat (apply is_comp || apply is_pair || apply is_copair)
                            ||
		                 (apply is_tpure    || apply is_lookup || apply is_update || 
	                          apply is_downcast || apply is_tag    || apply is_untag  || assumption)        
			    ||   
                                 (apply is_pure_ppg)
			    ||   
                                 (apply is_ppg_ctc)
                           ||    
                                 (apply is_pure_ro)
			    || 
		                 (apply is_ro_rw) 
                        ].

 Class PURE {A B: Type} (k: ekind) (f: term A B) := ispr : is (pure, k) f.
 Hint Extern 0 (PURE _)        => decorate : typeclass_instances.

 Class RO {A B: Type} (k: ekind) (f: term A B) := isro : is (ro, k) f.
 Hint Extern 0 (RO _)          => decorate : typeclass_instances.

 Class RW {A B: Type} (k: ekind) (f: term A B) := isrw : is (rw, k) f.
 Hint Extern 0 (RW _)          => decorate : typeclass_instances. 

 Class EPURE {A B: Type} (k: kind) (f: term A B) := isepr : is (k, epure) f.
 Hint Extern 0 (EPURE _)       => edecorate : typeclass_instances.

 Class PPG {A B: Type} (k: kind) (f: term A B) := isthrw : is (k, ppg) f.
 Hint Extern 0 (PPG _)  => edecorate : typeclass_instances.

 Class CTC {A B: Type} (k: kind) (f: term A B) := isctch : is (k, ctc) f.
 Hint Extern 0 (CTC _)     => edecorate : typeclass_instances.

End Make.


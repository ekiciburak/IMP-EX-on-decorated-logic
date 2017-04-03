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
Require Memory Terms Decorations Axioms Derived_co_Pairs Derived_co_Products.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.


Module Make(Import M: Memory.T).
  Module Export ProofsExp := Derived_co_Products.Make(M). 

(**STATES**)

 (** annihilation lookup-update *)
 Theorem ALU: forall i: Loc, 
         update i o lookup i === id.
         (* Prop: 2.1: All Cases *)
 Proof.
     intro i. apply local_global. intro k.
     destruct (Loc_dec i k) as [e|n]. rewrite <- e.
     (*Case k = i*)
     rewrite assoc.
     rewrite ax1, ids, idt. reflexivity.
     (*Case k <> i*)
     rewrite assoc. rewrite ax2; [| exact n].
       rewrite <- assoc. rewrite ss_unit; [| edecorate].
       cut (forget === id). intro H1. rewrite H1.
       reflexivity.
       (* forget == id *)
         symmetry. apply ss_unit. decorate.
 Qed.

 (** interaction lookup-lookup *)
 Theorem ILL: forall i,
         lookup i o forget o lookup i === lookup i.
         (* Prop: 2.2: All Cases: Simplified Version *)
 Proof.
     intro i. rewrite <- assoc.
       rewrite ss_unit; [| edecorate].
         cut (forget === id).
         intro H0. rewrite H0, ids. reflexivity.
           symmetry. apply ss_unit; decorate.
 Qed.

 (** interaction update-update *)
 Theorem IUU: forall (x: Loc) (p q: Z), 
         (update x o constant q) o (update x o constant p) === update x o constant q.
         (* Prop: 2.3: IMP+Exc adapted version *)
 Proof. intros x p q. apply local_global.
          intro i. destruct(Loc_dec i x). rewrite e.
            (* i = x *)
            repeat rewrite assoc. rewrite ax1. setoid_rewrite idt.
            setoid_rewrite <- ids at 6. rewrite <- assoc. apply (@pwsrepl _ _ _ epure); [decorate |].
            apply ws_unit.
            (* i<>x *)
            repeat rewrite assoc. rewrite ax2; [| auto].
            setoid_rewrite <- assoc at 4.
            setoid_rewrite <- assoc at 3.
            cut(forget o constant q === (@id unit)).
              intro H. rewrite H. setoid_rewrite ids at 1.
              rewrite ax2; auto. repeat rewrite <- assoc. apply sstows.
              apply replsubs; [reflexivity |].
              setoid_rewrite ss_unit; [reflexivity| decorate| decorate].
            (*1st cut*)
             setoid_rewrite ss_unit; [reflexivity| decorate| decorate].
 Qed.

 (** interaction update-lookup *)
 Theorem IUL: forall i: Loc,
         lookup i o update i ~== id. (* Prop: 2.4: All Cases *)
 Proof. intro i. apply ax1. Qed.

(*
 Theorem commutation_lookup_lookup: forall i j: Loc, i<>j ->
         (lprod id (lookup j)) o (inv_pi1 o lookup i)
         === 
         permut o (lprod id (lookup i)) o (inv_pi1 o lookup j). 
         (* Prop: 2.5: All Cases *)
 Proof.
    intros i j n. apply lpair_u. split.
    (*Case pi1*)
    unfold lprod at 1. rewrite assoc. 
    rewrite w_lpair_eq; [| decorate].
      rewrite idt.
      unfold inv_pi1 at 1.
    rewrite assoc, w_lpair_eq; [| decorate].
      rewrite idt.
    unfold permut, lprod. rewrite assoc. setoid_rewrite assoc at 2.
      rewrite w_lpair_eq; [| decorate].
    rewrite assoc, s_lpair_eq; [| decorate].
    do 2 rewrite <- assoc. setoid_rewrite assoc at 2. unfold inv_pi1.
      rewrite s_lpair_eq; [| decorate].
    rewrite s_unit; [| decorate].
    cut (forget == (@id unit)). intro H. rewrite H.
      rewrite ids. reflexivity.
    (*1st cut*)
    symmetry. apply s_unit; decorate.
    (*Case pi2*)
    unfold lprod at 1.
    rewrite assoc. rewrite s_lpair_eq; [| decorate].
    unfold inv_pi1 at 1.
    rewrite <- assoc. setoid_rewrite assoc at 2.
    rewrite s_lpair_eq; [| decorate].
    rewrite s_unit; [| decorate].
      cut (forget == (@id unit)).
      intro H. rewrite H. rewrite ids.
      unfold permut, lprod. do 3 rewrite assoc.
        rewrite s_lpair_eq; [| decorate].
        rewrite <- assoc.
        apply wtos; [decorate| decorate| ].
        rewrite w_lpair_eq, idt; [| decorate].
        unfold inv_pi1. rewrite assoc.
        rewrite w_lpair_eq; [rewrite idt; reflexivity| decorate]. 
      (*1st cut*)
      symmetry. apply s_unit; decorate.
 Qed.
*)

 (** commutation update-update *)
 Lemma CUU: forall {x y: Loc}, forall (n m: Z), x<>y -> 
	(update y o constant m) o (update x o constant n) === 
        (update x o constant n) o (update y o constant m).
         (*Prop 2.6: IMP+Exc adapted version.*)
 Proof.
    intros x y n m H0. apply local_global.
      intro i. destruct (Loc_dec i y). rewrite e.
        (* i = y *)
        repeat rewrite assoc. rewrite ax1.
        apply wssym. rewrite  ax2; [| decorate].
        setoid_rewrite <- assoc at 3.
        cut(forget o constant n === (@id unit)).
          intro H1. rewrite H1.
          setoid_rewrite ids. rewrite ax1.
          setoid_rewrite idt. rewrite <- assoc. setoid_rewrite <- ids at 1.
          apply (@pwsrepl _ _ _ epure); [decorate |].
          apply ws_unit; reflexivity.
        (*1st cut*)
        setoid_rewrite ss_unit; [reflexivity| decorate| decorate ].
        destruct (Loc_dec i x). rewrite e.
        (* i = x and i <> y*)
        repeat rewrite assoc. rewrite ax1.
        rewrite  ax2; [| auto].
        setoid_rewrite <- assoc at 3.
        cut(forget o constant m === (@id unit)).
          intro H1. rewrite H1.
          setoid_rewrite ids. rewrite ax1.
          setoid_rewrite idt. rewrite <- assoc. setoid_rewrite <- ids at 1.
          apply (@pwsrepl _ _ _ epure); [decorate |].
          apply ws_unit; reflexivity.
        (*2nd cut*)
        setoid_rewrite ss_unit; [reflexivity| decorate| decorate ].
        (* i <> x and i <> y *)
        repeat rewrite assoc. setoid_rewrite ax2; [| auto| auto].
        setoid_rewrite <- assoc at 3. setoid_rewrite <- assoc at 5.
        cut(forget o constant m === (@id unit)).
          intro H1. rewrite H1.
          setoid_rewrite ids. rewrite ax2; [| auto]. rewrite <- assoc.
          cut(forget o constant n === (@id unit)).
            intro H2. rewrite H2.
            setoid_rewrite ids. rewrite ax2; [| auto]. rewrite <- assoc. rewrite H1.
            rewrite ids. reflexivity.
          (*3rd cut*)
          setoid_rewrite ss_unit; [reflexivity| decorate| decorate ].
        (*4th cut*)
        setoid_rewrite ss_unit; [reflexivity| edecorate| decorate ].
 Qed.

 (** commutation lookup-constant *)
 Theorem CLC: forall (i: Loc) (c: Z), 
         (lookup i o (update i o (constant c)))
         === 
         (constant c) o update i o (constant c).
         (*Prop 2.8: All Cases*)
 Proof.
     intros i c. apply effect.
     (* Case 1: <> o f == <> o g *)
     rewrite assoc.
     cut (forget o lookup i === (@id unit)).
       intro H. rewrite H, idt.
       do 2 rewrite assoc.
       cut (forget o constant c === (@id unit)).
         intro H1; rewrite H1, idt.
         reflexivity.
       (*1st cut*)
       setoid_rewrite ss_unit; [reflexivity| decorate| decorate].
     (*2nd cut*)
     setoid_rewrite ss_unit; [reflexivity| edecorate| decorate].
     (* Case 2: f ~ g *)
     rewrite assoc, ax1, idt. setoid_rewrite <- ids at 1. rewrite <- assoc.
     apply (@pwsrepl _ _ _ epure); [decorate |].
     apply ws_unit.
 Qed.

 (** interactcommutation lookup-update-update *)
 Lemma CLUC: forall (m: Loc) (p q: Z),
      (pair (lookup m) (constant q)) o (update m o constant p)
      ===
      (pair (constant p) (constant q)) o (update m o constant p).
 Proof.
      intros m p q.
        apply ss_lpair_u.
          (*pi1 o f === pi1 o g*)
          setoid_rewrite assoc. setoid_rewrite fst_lpair_eq; [| decorate| decorate| decorate| decorate].
          rewrite CLC, assoc. reflexivity.
          (*pi2 o f === pi2 o g*)
          setoid_rewrite assoc. setoid_rewrite snd_lpair_eq; [reflexivity| decorate| decorate| decorate| decorate]. 
 Qed.

(*
 Lemma commutation_constant_lookup_update: forall (m: Loc) (p q: Z),
      (pair (constant q) (lookup m)) o (update m o constant p)
      ===
      (pair (constant q) (constant p)) o (update m o constant p).
 Proof.
      intros. apply (strong_pair3 epure). repeat rewrite assoc. remember wsrc.
      rewrite pair1;  try decorate. apply ws_sym.
      rewrite pair1;  try decorate. apply weak_refl.
      repeat rewrite assoc. remember ssc.
      rewrite pair2;  try decorate.  
      specialize(@commutation_lookup_constant m p). intros.
      setoid_rewrite <- assoc. rewrite H. apply strong_sym.
      rewrite pair2;  try decorate. apply ss_refl.
 Qed. 
*)

(**EXCEPTIONS**)

(*
 Lemma propagator_propagates_1: forall X Y (g: term Y X), PPG rw g -> g o (@empty X) === (@empty Y). 
 Proof. intros X Y g H. setoid_rewrite ss_empty; [reflexivity| decorate]. Qed.

 Lemma propagator_propagates_2: forall X Y (g: term Y X), PPG rw g -> g === (copair g (@empty Y)) o in1. 
 Proof.
    intros X Y g H. apply (@swtoss _ _ rw); [edecorate| edecorate| ]. apply swsym.
    apply (@sw_lcopair_eq _ _ _ rw); edecorate.
 Qed.
*)

 (** annihilation tag-untag *)
 Lemma ATU: forall e: EName, (tag e) o (untag e) === (@id Empty_set).
 Proof.
    intro e.
    apply elocal_global.
    intro r. destruct(Exc_dec r e) as [Ha|Hb]. rewrite Ha.
    (* case e = r *) (* (1) *)
    rewrite idt. setoid_rewrite <- ids at 6. rewrite <- assoc. (* (1.1) *)
    apply swrepl; [reflexivity| apply eax1]. (* (1.2) *)
    (* case e <> r *) (* (2) *)
    cut(tag e o (@empty unit) === (@id (Empty_set)));
      [ intro H0| setoid_rewrite ss_empty; [reflexivity| decorate| edecorate]].
    rewrite <- H0. setoid_rewrite <- assoc. (* (2.1) *)
    apply swrepl; [reflexivity| apply eax2; exact Hb]. (* (2.2) *)
Qed.

 (** commutation untag-untag *)
 Lemma CUUe: forall (t s: EName) , s <> t -> 
    (rcoprod (untag t) id) o in2 o (untag s) === (lcoprod id (untag s)) o in1 o (untag t).
 Proof.
    intros. apply elocal_global. intro r.  
    (* r = t /\ r <> s *)
    destruct(Exc_dec r s). rewrite e. setoid_rewrite <- assoc at 4. rewrite (@eax2 s t); [| exact H].
      setoid_rewrite <- assoc at 4. setoid_rewrite assoc at 2.
      cut (in1 o (@empty unit) === in2).
        intro H1. rewrite H1.
        rewrite assoc, (@ss_lcoprod_eq _ _ _ _ pure); [| edecorate| edecorate].
        setoid_rewrite <- assoc. rewrite eax1.
        setoid_rewrite ids. rewrite (@sw_rcoprod_eq _ _ _ _ pure); [| edecorate| edecorate].
        rewrite ids. reflexivity.
      (*1st cut*)
      setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate].
     
     destruct(Exc_dec r t). rewrite e. setoid_rewrite <- assoc. rewrite (@eax2 t s); [| auto].
       setoid_rewrite <- assoc. setoid_rewrite assoc at 2.
        cut (in2 o (@empty unit) === in1).
          intro H1. rewrite H1.
          rewrite assoc, ss_rcoprod_eq; [| edecorate| edecorate].
          setoid_rewrite <- assoc. rewrite eax1.
          setoid_rewrite ids. rewrite sw_lcoprod_eq; [| edecorate| edecorate].
          rewrite ids. reflexivity.
      (*2nd cut*)
      setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate].

     setoid_rewrite <- assoc. rewrite (@eax2 r s); [| auto].
       setoid_rewrite <- assoc. setoid_rewrite assoc at 2.
        cut (in2 o (@empty unit) === in1).
          intro H1. rewrite H1.
          rewrite assoc, ss_rcoprod_eq; [| edecorate| edecorate].
          setoid_rewrite <- assoc. 
          rewrite (@eax2 r t); [| auto].
          setoid_rewrite assoc at 3.
          cut (in1 o (@empty unit) === in2).
            intro H2. rewrite H2.
            setoid_rewrite assoc at 2. rewrite ss_lcoprod_eq; [| edecorate| edecorate].
            setoid_rewrite <- assoc. rewrite eax2; [| auto].
            apply sstosw. setoid_rewrite assoc. apply replsubs; [| reflexivity].
            setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate].
          (*4th cut*)
          setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate]. 
        (*3rd cut*)
        setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate].
Qed.

 (** annihilation catch-raise *)
 Lemma ACR: forall (l: EName), forall (X Y: Type) (f: term Y X), PPG rw f ->
 downcast ((copair id ((empty Y o tag l) o untag l) o in1) o f) === f.
 Proof.
    intros. apply (@swtoss _ _ rw); [decorate | edecorate |].
    rewrite <- sw_downcast.
    apply sstosw. setoid_rewrite <- assoc.
    transitivity(copair id ((@empty Y) o id) o in1 o f).
      rewrite assoc. apply replsubs; [| reflexivity]. apply replsubs; [| reflexivity]. 
        apply ss_lcopair_u.
          setoid_rewrite sw_lcopair_eq; [reflexivity| edecorate| edecorate].
          setoid_rewrite (@ss_lcopair_eq _ _ _ pure); [| edecorate| edecorate].
          rewrite <- assoc. rewrite ATU. reflexivity.
        setoid_rewrite <- idt at 10. apply replsubs; [| reflexivity].
        apply (@swtoss _ _ rw); [edecorate| edecorate |].
        apply (@sw_lcopair_eq _ _ _ pure); edecorate.
 Qed.

 Axiom mono: forall {X Y: Type} (f g: term Empty_set Y), PPG rw f /\ PPG rw g -> ((@empty X) o f === (@empty X) o g)-> f === g.


(*propagate*)
 Lemma PPT: forall X Y (e: EName) (a: term Y X), PPG rw a -> a o ((@empty X) o tag e) === (@empty Y) o tag e.
 Proof.
    intros X Y e a H.
    rewrite assoc. apply replsubs; [| reflexivity]. apply ss_empty; edecorate.
 Qed.


(*recover*)
 Lemma RCV: forall X Y (e: EName) (u1 u2: term unit Y), EPURE rw u1 -> EPURE rw u2 ->
            ((@empty X) o tag e) o u1 === ((@empty X) o tag e) o u2 -> u1 ===  u2.
 Proof.
    intros X Y e u1 u2 H0 H1 H2. setoid_rewrite <- assoc in H2.
      apply mono in H2; [| split; apply is_comp; [decorate| edecorate | decorate | edecorate ]].
      apply (@swtoss _ _ rw); [edecorate| edecorate| ].
        transitivity ((untag e o tag e) o u1). setoid_rewrite <- idt at 1.
          apply (@pswsubs _ _ _ rw). apply swsym, eax1. unfold pure_id. 
            split; [exact H0| reflexivity].
        apply swsym.
        transitivity ((untag e o tag e) o u2). setoid_rewrite <- idt at 1.
      apply (@pswsubs _ _ _ rw). apply swsym, eax1. unfold pure_id. 
            split; [exact H1| reflexivity].
        apply swsym. apply sstosw. setoid_rewrite <- assoc.
        apply replsubs; [reflexivity| exact H2].
 Qed.

(*try0*)
 Lemma TRY0: forall X Y (e: EName) (u: term Y X) (b: term Y unit), EPURE rw u -> PPG rw b ->
         downcast ((copair id (b o untag e) o in1) o u) === u.
 Proof.
    intros X Y e u b H0 H1.
      apply (@swtoss _ _ rw); [decorate |edecorate| ].
      rewrite <- sw_downcast. 
        transitivity(id o u). apply (@pswsubs _ _ _ rw); [| split; [exact H0| reflexivity]].
        apply (@sw_lcopair_eq _ _ _ rw); edecorate.
      rewrite idt. reflexivity.
 Qed.

(*try1*)
 Lemma TRY1: forall X Y (e: EName) (u: term unit X) (b: term Y unit), EPURE rw u -> PPG rw b ->
            downcast ((copair id (b o untag e) o in1) o ((empty Y o tag e) o u)) === b o u.
 Proof.
    intros X Y e u b H0 H1.
      apply (@swtoss _ _ rw); [decorate |edecorate| ].
      rewrite <- sw_downcast.
      do 2 setoid_rewrite assoc. setoid_rewrite <- assoc at 3.
      cut (in2 === in1 o (@empty Y)).
        intro H2. rewrite <- H2.
        rewrite ss_lcopair_eq; [| edecorate].
        apply (@pswsubs _ _ _ rw); [| split; [exact H0| reflexivity]].
        rewrite <- assoc. rewrite eax1, ids. reflexivity.
      setoid_rewrite ss_empty; [reflexivity| edecorate| edecorate].
 Qed.


(* -------------------- End of Main Proofs -------------------- *)

End Make.
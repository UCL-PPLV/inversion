From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple div fintype.

(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

Section States.

Structure state (sType : Type) :=  State {
  sContent : seq sType
}.

Definition mt_state : state False := State _ [::].

Structure world := World {
  wType : Type;
  coherent : state wType -> Prop;
  change : state wType -> state wType
}.

Definition mt_world := World _ (fun s => s = mt_state) (fun x => x).

Goal @coherent mt_world mt_state.
Proof. by done. Qed.

Structure packed_state := PState {
  pType : Type;
  pState : state pType                            
}.

Definition pstates := seq (nat * packed_state).
Definition worlds := seq (nat * world).

Definition get {T} (x0 : T) (s : seq (nat * T)) l :=
  let: n := find (fun z => fst z == l) s in
  if n < length s then snd (nth (n, x0) s l) else x0.                 

Definition gets (s : pstates) := get (PState _ mt_state) s. 
Definition getw (w : worlds) := get mt_world w.

Definition keys {T} (s : seq (nat * T)) := map (fun e => fst e) s.

(* Pre-coherence, types are equal *)
Definition coh1 (w : worlds) (s : pstates) :=
  keys w = keys s /\
  forall l, pType (gets s l) = wType (getw w l).

Definition cast (t t' : Type) (r : t = t') (e : t) : t' :=
  match r in (_ = t') return t' with erefl => e end.
  
Require Import Eqdep.
Definition castK m (r : m = m) (e : m) : cast _ _ r e = e.
Proof. by move: r; apply: Streicher_K. Qed.

Lemma cohE w s : coh1 w s ->
                 forall l, state (pType (gets s l)) = state (wType (getw w l)).
Proof. by case=>C1 C2  l; move: (C2 l)=>->. Qed.

(* Since we know that the state's type is the same as the world's, we can assure it's coherent *)
Definition coh2 (w : worlds) (s : pstates) (C1 :  coh1 w s):=
  forall l, @coherent (getw w l) (cast _ _ (cohE _ _ C1 l) (pState (gets s l))).

(* Overall coherence is a dependent product. *)
Definition coh (w : worlds) (s : pstates) := exists C1: coh1 w s, coh2 _ _ C1.

Lemma get_mt {T} (x0 : T) l : get x0 [::] l = x0.
Proof. by []. Qed.

(* Okay, now let's prove something trivial *)

(* REM: The following proof works if we just evaluate gets [::] l: *)
Lemma coh_empty : coh [::] [::].
Proof.
have C1: coh1 [::] [::] by []. 
exists C1=>l.
by simpl; apply: castK.
Qed.

Set Injection On Proofs.


(* A simpler version of the same goal, with "get" stripped off *)
Lemma X : forall (G : state (pType {| pType := False; pState := mt_state |}) = state False),
    cast (state (pType {| pType := False; pState := mt_state |}))
         (state False) G mt_state = mt_state.
have E: pType {| pType := False; pState := mt_state |} = False by [].
rewrite /cast.

injection E.

(* Okay, how can we now rewrite the equality in the type of G without
   reducing it explicitly? *)


Lemma Y : forall l (C1 : coh1 [::] [::]),
  coherent (get mt_world [::] l)
    (cast (state (pType (get {| pType := False; pState := mt_state |} [::] l)))
       (state (wType (get mt_world [::] l))) (cohE [::] [::] C1 l)
       (pState (get {| pType := False; pState := mt_state |} [::] l))).
move=>l C1.
move: (get_mt {| pType := False; pState := mt_state |} l) => H. 

(*

"injection" is Coq's standard tactic, ssreflect's version would be
"case". See ssrfelect manual for the explanation of the relation
vetween the two (https://hal.inria.fr/inria-00258384)

After trying it, the following cryptic message is given:

"Error: No information can be deduced from this equality and the
injectivity of constructors. This may be because the terms are
convertible, or due to pattern matching restrictions in the sort
Prop."

Perhaps, we should investigate how the injection works here. According
to Adam's page

http://adam.chlipala.net/itp/tactic-reference.html

the equality shoud be indeed between elements of two constructors,
but, here there are no constructors, jsut the equality.

*)

injection H.



Defined.
Print X.


(* However, an attempt to prove it by rewriting gloriously fails: *)
Lemma coh_empty' : coh [::] [::].
Proof.
have C1: coh1 [::] [::] by []. 
exists C1=>l.
(* let's now do some rewriting in the goal, but no simplification: *)
rewrite /gets/getw.


(* The following rewriting should fire in the goal, although it
doesn't, and fails on the dependent error. *)

(* 

(* ssreflect rewriting fails*) 
rewrite get_mt. 

*)

(*

(* And so does Coq's dependent rewiriting *)

have X: get mt_world [::] l = mt_world by apply: get_mt.
dependent rewrite -> X.

 *)

Admitted.




Lemma get_cat {T} (x0 : T) (s1 s2 : seq (nat * T)) l :
  get x0 (s1 ++ s2) l = if l \in keys s1 then get x0 s1 l else get x0 s2 l.                                                
Proof.
(* OKay, this should be true, but I'm too lazy to prove it now *)
Admitted.

(* Let's prove something more complicated. *)
Lemma coh_cat w1 w2 s1 s2 :
  coh w1 s1 -> coh w2 s2 -> coh (w1 ++ w2) (s1 ++ s2).
Proof.
move=>C1 C2.
have X1: keys (w1 ++ w2) = keys (s1 ++ s2).
- case: C1; case=>H1 _ _; case: C2; case=>H2 _ _.
  by rewrite /keys in H1 H2 *; rewrite !map_cat H1 H2. 
have X2: coh1 (w1 ++ w2) (s1 ++ s2).
- split=>// l; rewrite /gets/getw.
  case: C1; case=>H1 G1 _; case: C2; case=>H2 G2 _.
  by rewrite !get_cat H1; case: ifP=>H; [apply: G1 | apply:G2].
(* Now the real fun begins. *)
exists X2=>l; rewrite /gets/getw.  

(* Two direct equalities we would like to use for rewriting *)
have Es: get (PState _ mt_state) (s1 ++ s2) l =
   if l \in keys s1 then get (PState _ mt_state) s1 l else get (PState _ mt_state) s2 l
by rewrite get_cat.  

have Ew: get mt_world (w1 ++ w2) l =
   if l \in keys s1 then get mt_world w1 l else get mt_world w2 l
by rewrite get_cat; case: (C1); case=>H1 G1 _; rewrite H1.



(* Butwe can't because of the depented type error! *)
rewrite Ew.




  

End States.

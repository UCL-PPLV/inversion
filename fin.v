From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple div fintype.

(* Reasoning about finite types without indexed type families.
   Inspired by this James' post:

https://homes.cs.washington.edu/~jrw12/dep-destruct.html

Check for [REM]s in the code below for some ideas and insights.

Some main ideas so far:

* Using inductive type families with parameters and explicit
  equalities instead of indices; this leads to proof obligations with
  different proofs of an equality, which, ideally, shoudl be
  discharged via the Streicher K axiom;

* Since nat has decidable equality, we can don't need the full-blown K
  axiom, and cen get away with ssreflect's eq_axiomK lemma. The proof
  of this lemma is by building a simple discriminator on the two
  possible constructors or reflect (x = y) (x == y).
  (akin to https://syntaxexclamation.wordpress.com/2013/12/04/1-%E2%89%A0-0/)
*)


(* [REM] Working with indexed type families is painful, as they hide
   the equalities. Instead, I reformulate the finite type definition
   from James' post making the equalities explicit. *)
Inductive Fin (n : nat) : Set :=
  F1 m of n = m.+1
| FS m of n = m.+1 & Fin m.

Definition f21 : Fin 2 := F1 2 _ (erefl _).
Definition f22 : Fin 2 := FS 2 1 (erefl _) (F1 1 _ (erefl _)).

Definition cardinality (n : nat) (A : Type) : Prop :=
  exists (f : A -> Fin n) (g : Fin n -> A),
    (forall x, g (f x) = x) /\
    (forall y, f (g y) = y).

Definition bool_to_Fin_2 (x : bool) : Fin 2 :=
  if x then f22 else f21.

Definition Fin_2_to_bool (y : Fin 2) : bool :=
  match y with
  | F1 _ _ => false
  | FS _ _ _ => true
  end.

Require Import Program.

Lemma fin1_eq (f1 f2 : Fin 1) : f1 = f2.
case: f1=>m E; case: (E)=>Z; subst m; last by case. 
case: f2=> m' E'; case: (E')=>Z; subst m'; last by case.
(* [REM] Since equpality for nat is decidable, we don't need the
         full-blown K axiom to equate equality proofs. *)
move: (eq_axiomK E) (eq_axiomK E')=>//= Z1 Z2. 
by subst E E'. 
Qed.

Theorem bool_cardinality_2 :
  cardinality 2 bool.
Proof.
exists bool_to_Fin_2, Fin_2_to_bool; split; [by case|move=>y].
case: y=>m E/=; case: (E)=>Z; subst m. 
- by rewrite /f21; move: (eq_axiomK E)=>//= Z; subst E.
move=> f. move: (eq_axiomK E)=>/=Z; subst E.
by move: (fin1_eq f ((F1 1 0 (erefl 1))))=>Z; subst f. 
Qed.

(* [REM] Note to self: check how [subst] and [rewrite] tactics work,
   i.e., how exactly do they employ equality proofs. *)

(* Okay, now how to do the same with an indexed type family *)

(* An indexed family for the finite type *)
Inductive Fin' : nat -> Set :=
  F1' : forall n : nat, Fin' (n.+1)
| FS' : forall n : nat, Fin' n -> Fin' (n.+1).

(* [Q] How to get from definition Fin' to the definition Fin with
   explicit equalities? *)

(* Goal forall f1 f2 : Fin' 1, f1 = f2. *)
(* move=> f1 f2. *)
(* dependent inversion f1. *)
(* (* FAIL *) *)

(* Some experiments with converting equalities. *)
Inductive type : Type :=  Nat : type | Func : type -> type -> type.


Lemma ty_eq_dec :
  forall x y : type, {x = y} + {x <> y}.
Proof.
decide equality.
Qed.

Definition typeEq : rel type :=
  fun x y =>
    match ty_eq_dec x y with
    | left _ => true
    | right _ => false
    end.

Lemma typeP: Equality.axiom typeEq.
Proof.
by move=>x y; rewrite /typeEq; case: (ty_eq_dec x y)=>H;
   [constructor 1 | constructor 2].
Qed.

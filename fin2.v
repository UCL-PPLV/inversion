From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun seq tuple div fintype.

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

(* stolen and adapted some convenience definition from http://muaddibspace.blogspot.be/2008/12/axiom-free-noconfusion-in-coq.html *)
Ltac prove_noConfusion :=
  intros;
    match goal with Eql : ?x = _ |- _ =>
      elim Eql; elim x; simpl; tauto end.

(*
Inductive nat : Set :=
| O : nat
| S : nat -> nat.
*)

Definition NoConfusion_nat (x y : nat) : Type :=
  match x, y with
    | O, O => True
    | O, S y => False
    | S x, O => False
    | S x, S y => x = y
  end.

(* See McBride-al:TYPES04 *)
Definition noConfusion_nat (x y : nat) :
  x = y -> NoConfusion_nat x y := 
  (match x return forall y, x = y -> NoConfusion_nat x y with
     | 0 => fun y e => eq_rect 0 (NoConfusion_nat 0) I y e
     | S x' => fun y e => eq_rect (S x') (NoConfusion_nat (S x')) eq_refl y e
   end) y.

Definition noConfInv_nat (x y : nat) : NoConfusion_nat x y -> x = y :=
  (match x return forall y, NoConfusion_nat x y -> x = y with
    | 0 => fun y => match y with
                      | 0 => fun e => eq_refl
                      | S y' => fun f => False_rect (0 = S y') f
                    end
    | S x' => fun y => match y with
                         | 0 => fun f => False_rect (S x' = 0) f
                         | S y' => fun e => f_equal S e
                       end
  end) y.

Definition J (A : Type) (x : A) (P : forall y, x = y -> Type) (Pe : P x eq_refl) y (e : x = y) : P y e :=
  match e with | eq_refl => Pe end.

Definition noConf_nat_linv (x y : nat) (e : x = y) : noConfInv_nat x y (noConfusion_nat x y e) = e :=
  (match x return forall y (e : x = y), noConfInv_nat x y (noConfusion_nat x y e) = e with
    | 0 => fun e => J nat 0 (fun y' e' => noConfInv_nat 0 y' (noConfusion_nat 0 y' e') = e') eq_refl e
    | S x' => fun e => J nat (S x') (fun y e => noConfInv_nat (S x') y (noConfusion_nat (S x') y e) = e) eq_refl e
  end) y e.

  
Set Implicit Arguments.


Definition injectivity_nat_suc :
  forall x y (P : S x = S y -> Type)
         (H : forall (e : x = y), P (noConfInv_nat (S x) (S y) e))
         (e : S x = S y), P e.
  move=> x y P H e.
  refine (eq_rect (noConfInv_nat (S x) (S y) (noConfusion_nat (S x) (S y) e))
                  P (H (noConfusion_nat (S x) (S y) e)) e _).
  by apply noConf_nat_linv.
Defined.

Lemma fin1_eq (f1 f2 : Fin 1) : f1 = f2.
  case: f1=>m; refine (injectivity_nat_suc _ _)=> e; subst m; last by case.
  by case: f2=> m'; refine (injectivity_nat_suc _ _) => e; subst m'=>//=; case. 
Qed.

(* old fin1_eq proof was 2 lines longer:
Lemma fin1_eq (f1 f2 : Fin 1) : f1 = f2.
case: f1=>m E; case: (E)=>Z; subst m; last by case. 
case: f2=> m' E'; case: (E')=>Z; subst m'; last by case.
(* [REM] Since equpality for nat is decidable, we don't need the
         full-blown K axiom to equate equality proofs. *)
move: (eq_axiomK E) (eq_axiomK E')=>//= Z1 Z2. 
by subst E E'. 
Qed.
*)
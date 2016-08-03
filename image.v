From mathcomp.ssreflect
Require Import ssreflect ssrbool.

Set Implicit Arguments.

(* Example 4 from "Unifiers as Equivalences" *)

Inductive Im (A B : Type) (f : A -> B) (y : B) : Type :=
  image x of y = f x.

(* when would we need the following lemma?  Perhaps if the above image proofs are used inside the encoding of a different relation? *) 
Lemma im_prop : forall (A B : Type) (f : A -> B) (x x' : A) (e : f x = f x'), eq_rect (f x) (fun y => Im f y) (image f x eq_refl) (f x') e = image f x' eq_refl -> x = x'.
Proof.
  move=> A B f x x' e eqims.
  (* cannot use e, cannot use eqims...*)
Admitted.



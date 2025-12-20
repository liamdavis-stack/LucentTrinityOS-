(*--------------------------------------------------------------------*)
(*  M15 Hilbert Space Skeleton (Coq Nano)                              *)
(*                                                                    *)
(*  This nano defines the ambient 15-dimensional real vector space    *)
(*  used by the LTOS quantum kernel.                                  *)
(*                                                                    *)
(*  It is intentionally minimal and public-facing: a clean skeleton   *)
(*  that can later be refined with a concrete finite-dimensional       *)
(*  vector library (e.g., Vector.t R 15, mathcomp, or Coquelicot).    *)
(*--------------------------------------------------------------------*)

Require Import Reals.

(* M15 is declared as an abstract 15-dimensional real vector space. *)
Parameter M15 : Type.

(* Scalar multiplication *)
Parameter smul : R -> M15 -> M15.

(* Vector addition *)
Parameter vadd : M15 -> M15 -> M15.

(* Zero vector *)
Parameter vzero : M15.

(* Axioms for vector space structure *)
Axiom vadd_assoc : forall a b c : M15, vadd a (vadd b c) = vadd (vadd a b) c.
Axiom vadd_comm  : forall a b : M15, vadd a b = vadd b a.
Axiom vadd_zero  : forall a : M15, vadd a vzero = a.
Axiom vadd_neg   : forall a : M15, exists b : M15, vadd a b = vzero.

Axiom smul_dist_vadd :
  forall r a b, smul r (vadd a b) = vadd (smul r a) (smul r b).

Axiom smul_dist_radd :
  forall r s a, smul (r + s) a = vadd (smul r a) (smul s a).

Axiom smul_assoc :
  forall r s a, smul (r * s) a = smul r (smul s a).

Axiom smul_one :
  forall a, smul 1 a = a.
(*--------------------------------------------------------------------*)
(*  M15 Hilbert Space Skeleton (Coq Nano)                              *)
(*                                                                    *)
(*  This nano defines the ambient 15-dimensional real vector space    *)
(*  used by the LTOS quantum kernel.                                  *)
(*                                                                    *)
(*  It is intentionally minimal and public-facing: a clean skeleton   *)
(*  that can later be refined with a concrete finite-dimensional       *)
(*  vector library (e.g., Vector.t R 15, mathcomp, or Coquelicot).    *)
(*--------------------------------------------------------------------*)

Require Import Reals.

(* M15 is declared as an abstract 15-dimensional real vector space. *)
Parameter M15 : Type.

(* Scalar multiplication *)
Parameter smul : R -> M15 -> M15.

(* Vector addition *)
Parameter vadd : M15 -> M15 -> M15.

(* Zero vector *)
Parameter vzero : M15.

(* Axioms for vector space structure *)
Axiom vadd_assoc : forall a b c : M15, vadd a (vadd b c) = vadd (vadd a b) c.
Axiom vadd_comm  : forall a b : M15, vadd a b = vadd b a.
Axiom vadd_zero  : forall a : M15, vadd a vzero = a.
Axiom vadd_neg   : forall a : M15, exists b : M15, vadd a b = vzero.

Axiom smul_dist_vadd :
  forall r a b, smul r (vadd a b) = vadd (smul r a) (smul r b).

Axiom smul_dist_radd :
  forall r s a, smul (r + s) a = vadd (smul r a) (smul s a).

Axiom smul_assoc :
  forall r s a, smul (r * s) a = smul r (sm


(*--------------------------------------------------------------------*)
(*  Fixed Point Theorem for Christos Mediation (Coq Nano)             *)
(*                                                                    *)
(*  This nano proves the Coq analogue of the Lean theorem:            *)
(*                                                                    *)
(*      mediate c Omega = Omega                                       *)
(*                                                                    *)
(*  using only the abstract vector-space axioms from M15.v.           *)
(*--------------------------------------------------------------------*)

Require Import Reals.
Require Import M15.
Require Import Omega.
Require Import ChristosOperator.

Open Scope R_scope.

Lemma house_xviii_is_fixed_point :
  forall c : R, mediate c Omega = Omega.
Proof.
  intros c.
  unfold mediate.
  (* We want: vadd (smul (1 - c) Omega) (smul c Omega) = Omega *)
  (* Use vector-space axioms: (1 - c)B7N) + cB7N) = (1 - c + c)B7N) = 1B7N) = N) *)
  assert (H1 : vadd (smul (1 - c) Omega) (smul c Omega)
              = smul ((1 - c) + c) Omega).
  {
    (* This uses distributivity of smul over vadd *)
    rewrite <- smul_dist_radd.
    reflexivity.
  }
  rewrite H1.
  replace ((1 - c) + c) with 1 by field.
  rewrite smul_one.
  reflexivity.
Qed.


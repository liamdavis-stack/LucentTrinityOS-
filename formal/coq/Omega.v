(*--------------------------------------------------------------------*)
(*  Omega State (Coq Nano)                                            *)
(*                                                                    *)
(*  This nano introduces the Omega state as a distinguished element   *)
(*  of the ambient space M15, together with a normalization axiom.    *)
(*                                                                    *)
(*  It mirrors the Lean nano:                                         *)
(*    - Lean:  Omega : M15                                            *)
(*    - Lean:  omega_is_unit_statement, omega_is_unit                 *)
(*--------------------------------------------------------------------*)

Require Import Reals.
Require Import M15.

Open Scope R_scope.

(* A norm on M15, abstract at this stage. *)
Parameter vnorm : M15 -> R.

(* Omega: the distinguished LTOS state in M15. *)
Parameter Omega : M15.

(* Statement: Omega is normalized (unit norm). *)
Definition omega_is_unit_statement : Prop :=
  vnorm Omega = 1.

(* Axiom: Omega is a unit vector in M15. *)
Axiom omega_is_unit : omega_is_unit_statement.


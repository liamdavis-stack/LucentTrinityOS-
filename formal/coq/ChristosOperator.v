(*--------------------------------------------------------------------*)
(*  Christos Mediation Operator (Coq Nano)                             *)
(*                                                                    *)
(*  This nano defines the Christos mediation operator on the abstract *)
(*  15-dimensional vector space M15.                                  *)
(*                                                                    *)
(*  It mirrors the Lean definition:                                   *)
(*      mediate c s = (1 - c) b
" s + c b
" Omega                         *)
(*--------------------------------------------------------------------*)

Require Import Reals.
Require Import M15.
Require Import Omega.

Open Scope R_scope.

(* Christos mediation operator on M15. *)
Definition mediate (c : R) (s : M15) : M15 :=
  vadd (smul (1 - c) s) (smul c Omega).


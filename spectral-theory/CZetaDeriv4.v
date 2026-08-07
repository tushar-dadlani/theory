(* ================================================================= *)
(*  CZetaDeriv4.v  —  Milestone B, brick B4: the SECOND-derivative      *)
(*  series of zeta converges.  Exactly analogous to CZetaDeriv3's        *)
(*  dgtermC_cv (first-derivative series), one order up: the structural   *)
(*  second-derivative term d2gtermC has |d2gtermC s n| <= 2 d2bound s n  *)
(*  (Cmod_d2gtermC_bound) and Sum d2bound converges (d2bound_sum_cv),    *)
(*  so Sum d2gtermC converges absolutely on Re s > 0.  This is the       *)
(*  analytic-part convergence for zeta'' (= d/ds of zeta').              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CZetaTerm CZetaTerm2.
Open Scope R_scope.

(* the second-derivative series D2 = sum d2gtermC(s,n) converges on Re s>0 *)
Lemma d2gtermC_cv : forall s, 0 < Re s -> Cminus C1 s <> C0 ->
  { D2 | Cseries_cv (d2gtermC s) D2 }.
Proof.
  intros s Hs0 Hs1.
  apply (Cseries_abs_cv (d2gtermC s) (fun n => 2 * d2bound s n)).
  - intro n; apply Cmod_d2gtermC_bound; [ lra | exact Hs1 ].
  - destruct (d2bound_sum_cv s Hs0) as [T HT].
    exists (2 * T).
    replace (sum_f_R0 (fun n => 2 * d2bound s n))
      with (fun N => 2 * sum_f_R0 (d2bound s) N).
    + apply (CV_mult (fun _ => 2) (sum_f_R0 (d2bound s)) 2 T);
        [ apply Un_cv_const | exact HT ].
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (d2bound s) N 2); apply sum_eq; intros i _; ring.
Qed.

Print Assumptions d2gtermC_cv.

(* ================================================================= *)
(*  END CZetaDeriv4.v  —  the second-derivative series of zeta converges.*)
(* ================================================================= *)

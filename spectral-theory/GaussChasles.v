(* ================================================================= *)
(*  GaussChasles.v  —  Poisson→θ, Phase P2 (step 3): the Chasles       *)
(*  decomposition of ∫_{−N}^{N} into unit cells.                       *)
(*                                                                    *)
(*    chasles_R : ∫_0^{S M} sg = Σ_{n=0}^{M} ∫_n^{n+1} sg;             *)
(*    chasles_L : ∫_{−(S M)}^0 sg = Σ_{n=0}^{M} ∫_{−(n+1)}^{−n} sg.    *)
(*                                                                    *)
(*  (RiemannInt_P26 induction, bound reconciliation via RiemannInt_P5.)*)
(*  Feeding these cells through unit_shift / unit_shift_neg + RInt_sum  *)
(*  gives ∫_{−N}^{N} sg = ∫_0^1 (partial Θ_t)·cos.  No new axioms.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussPeriodCoeff.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Right half:  ∫_0^{S M} = Σ_{n≤M} ∫_n^{n+1}.                       *)
(* ----------------------------------------------------------------- *)

Lemma chasles_R : forall t m M
  (pr : Riemann_integrable (sg t (INR m)) 0 (INR (S M)))
  (cells : forall n, Riemann_integrable (sg t (INR m)) (INR n) (INR n + 1)),
  RiemannInt pr = sum_f_R0 (fun n => RiemannInt (cells n)) M.
Proof.
  intros t m M; induction M as [| M IH]; intros pr cells; cbn [sum_f_R0].
  - revert pr; replace (INR (S 0)) with (INR 0 + 1) by (simpl; ring);
      replace 0 with (INR 0) by (simpl; reflexivity); intro pr; apply RiemannInt_P5.
  - pose proof (RiemannInt_P26 (sg_int t (INR m) 0 (INR (S M)))
                  (sg_int t (INR m) (INR (S M)) (INR (S (S M)))) pr) as HP.
    assert (H1 : RiemannInt (sg_int t (INR m) 0 (INR (S M))) = sum_f_R0 (fun n => RiemannInt (cells n)) M)
      by (apply IH).
    assert (H2 : RiemannInt (sg_int t (INR m) (INR (S M)) (INR (S (S M)))) = RiemannInt (cells (S M))).
    { generalize (sg_int t (INR m) (INR (S M)) (INR (S (S M)))).
      assert (E : INR (S (S M)) = INR (S M) + 1) by (rewrite (S_INR (S M)); ring).
      rewrite E; intro p; apply RiemannInt_P5. }
    rewrite <- HP, H1, H2; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Left half:  ∫_{−(S M)}^0 = Σ_{n≤M} ∫_{−(n+1)}^{−n}.               *)
(* ----------------------------------------------------------------- *)

Lemma chasles_L : forall t m M
  (pr : Riemann_integrable (sg t (INR m)) (- INR (S M)) 0)
  (cells : forall n, Riemann_integrable (sg t (INR m)) (- INR (S n)) (- INR n)),
  RiemannInt pr = sum_f_R0 (fun n => RiemannInt (cells n)) M.
Proof.
  intros t m M; induction M as [| M IH]; intros pr cells; cbn [sum_f_R0].
  - revert pr; replace 0 with (- INR 0) by (simpl; ring); intro pr; apply RiemannInt_P5.
  - pose proof (RiemannInt_P26 (sg_int t (INR m) (- INR (S (S M))) (- INR (S M)))
                  (sg_int t (INR m) (- INR (S M)) 0) pr) as HP.
    assert (H1 : RiemannInt (sg_int t (INR m) (- INR (S M)) 0) = sum_f_R0 (fun n => RiemannInt (cells n)) M)
      by (apply IH).
    assert (H2 : RiemannInt (sg_int t (INR m) (- INR (S (S M))) (- INR (S M))) = RiemannInt (cells (S M)))
      by apply RiemannInt_P5.
    rewrite <- HP, H1, H2; ring.
Qed.

Print Assumptions chasles_R.
Print Assumptions chasles_L.

(* ================================================================= *)
(*  END GaussChasles.v (P2 step 3)                                  *)
(*  ∫_0^{S M} and ∫_{−(S M)}^0 split into their unit cells.  Next:      *)
(*  unit_shift / unit_shift_neg turn each cell into ∫_0^1 (shifted),    *)
(*  RInt_sum sums them into ∫_0^1 (partial Θ_t)·cos, and P1 gives       *)
(*  c_k = (1/√t)e^{−πk²/t}.                                            *)
(* ================================================================= *)

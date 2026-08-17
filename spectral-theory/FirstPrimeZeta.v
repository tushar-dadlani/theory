(* ================================================================= *)
(*  FirstPrimeZeta.v  —  2 is the first prime, connected to ζ on ℂ.       *)
(*                                                                    *)
(*  The CAPSTONE of the count-2 thread (CountTwoCollapse.v).  "Count = 2"  *)
(*  is the first prime; here the count-2 objects (2^inf, (-2)^inf, the     *)
(*  2-mode tower) are tied back to the Riemann ζ function — three faces of *)
(*  the first prime in ζ, plus the complex-plane bridge:                  *)
(*                                                                    *)
(*   (A) Prime-2 EULER FACTOR — ζ's first factor.  `euler_factor_2`:       *)
(*        Σ_k (2^{−s})^k → 1/(1−2^{−s})  (s>0; = the p=2 factor of the      *)
(*        Euler product ζ(s)=∏_p(1−p^{−s})^{−1}, CEulerProductFull.EF_cv).  *)
(*        COMPLEX bridge: `two_cpow_lt1` — the first prime's fugacity       *)
(*        |2^{−s}| = 2^{−Re s} < 1 ⟺ Re s > 0 (the '2^inf' on ℂ).          *)
(*   (B) The (-2)/ALTERNATING twist.  `alt_euler_factor_2`:                *)
(*        Σ_k (−2^{−s})^k → 1/(1+2^{−s})  — the '(-2)^inf' oscillation as   *)
(*        the alternating Euler factor at the first prime (the p=2 factor   *)
(*        of ζ(2s)/ζ(s) = Σ Liouville(n) n^{−s}).                          *)
(*   (C) The Fock 2-MODE TOWER.  `crea2_tower`: iterating creation on the   *)
(*        vacuum builds e_1,e_2,e_4,…=e_{2^k}; `fock2_euler`: summing       *)
(*        n^{−s} over that tower IS the Euler sub-trace → the (A) factor.   *)
(*                                                                    *)
(*  `first_prime_zeta` bundles (A)(B)(C); `whole_picture` ties Count = 2    *)
(*  (the cardinality) to all three ζ-connections and the collapse.         *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Ensembles Finite_sets.
Require Import Ell2Basis Ell2Zeta Ell2Euler Ell2Fock ComplexField Cmodulus CexpFull
        CountTwoCollapse.
Open Scope R_scope.

(* ===== (A) the prime-2 Euler factor = ζ's first factor ===== *)
Lemma euler_factor_2 : forall s, 0 < s -> Un_cv (euler_subtrace s 2) (/ (1 - z s 2)).
Proof. intros s Hs. apply euler_factor; [ lia | exact Hs ]. Qed.

(* complex bridge: the first prime's fugacity |2^{-s}| = 2^{-Re s}, <1 iff Re s>0 *)
Lemma two_cpow_mod : forall s : C, Cmod (Cpw 2 (Copp s)) = Rpower 2 (- Re s).
Proof. intro s. rewrite Cpw_mod. reflexivity. Qed.

Lemma two_cpow_lt1 : forall s : C, 0 < Re s -> Cmod (Cpw 2 (Copp s)) < 1.
Proof.
  intros s Hs. rewrite two_cpow_mod.
  replace 1 with (Rpower 2 0) by (apply Rpower_O; lra).
  apply Rpower_lt; lra.
Qed.

(* ===== (C) the Fock 2-mode occupation tower -> the Euler factor ===== *)
Lemma crea2_tower : forall k, Nat.iter k (crea 2) (e 1) = e (2 ^ k).
Proof.
  induction k as [| k IH]; [ reflexivity | ].
  simpl Nat.iter. rewrite IH, crea_e by lia. reflexivity.
Qed.

Lemma fock2_subtrace : forall s K, euler_subtrace s 2 K = sum_f_R0 (fun k => z s (2 ^ k)) K.
Proof.
  intros s K. rewrite euler_subtrace_eq by lia. apply sum_eq. intros k _.
  rewrite (zeta_pk s 2 k) by lia. reflexivity.
Qed.

Lemma fock2_euler : forall s, 0 < s ->
  Un_cv (fun K => sum_f_R0 (fun k => z s (2 ^ k)) K) (/ (1 - z s 2)).
Proof.
  intros s Hs. apply (Un_cv_ext (euler_subtrace s 2)).
  - intro K. apply fock2_subtrace.
  - apply euler_factor_2; exact Hs.
Qed.

(* ===== (B) the (-2)/alternating twist -> the alternating Euler factor ===== *)
Lemma alt_euler_factor_2 : forall s, 0 < s ->
  Un_cv (fun K => sum_f_R0 (fun k => (- z s 2) ^ k) K) (/ (1 + z s 2)).
Proof.
  intros s Hs.
  assert (Habs : Rabs (- z s 2) < 1) by (rewrite Rabs_Ropp; apply z_abs_lt1; [ lia | exact Hs ]).
  pose proof (geom_cv (- z s 2) Habs) as HG.
  replace (/ (1 - - z s 2)) with (/ (1 + z s 2)) in HG by (f_equal; lra).
  exact HG.
Qed.

(* ===== the capstone: the many faces of the first prime in ζ ===== *)
Theorem first_prime_zeta : forall s, 0 < s ->
  Un_cv (euler_subtrace s 2) (/ (1 - z s 2))
  /\ Un_cv (fun K => sum_f_R0 (fun k => (- z s 2) ^ k) K) (/ (1 + z s 2))
  /\ Un_cv (fun K => sum_f_R0 (fun k => z s (2 ^ k)) K) (/ (1 - z s 2)).
Proof.
  intros s Hs. repeat split.
  - apply euler_factor_2; exact Hs.
  - apply alt_euler_factor_2; exact Hs.
  - apply fock2_euler; exact Hs.
Qed.

(* ===== the whole picture: Count = 2 → first prime → ζ → collapse ===== *)
Theorem whole_picture : forall x y s : R, x <> y -> 0 < s ->
  cardinal R (pairR x y) 2                                              (* Count = 2 *)
  /\ Un_cv (euler_subtrace s 2) (/ (1 - z s 2))                         (* (A) first Euler factor *)
  /\ Un_cv (fun K => sum_f_R0 (fun k => (- z s 2) ^ k) K) (/ (1 + z s 2)) (* (B) (-2)-twist *)
  /\ Un_cv (fun K => sum_f_R0 (fun k => z s (2 ^ k)) K) (/ (1 - z s 2))  (* (C) Fock 2-mode tower *)
  /\ Un_cv (fun n => (x + y) / 2 ^ n) 0.                                (* the collapse *)
Proof.
  intros x y s Hxy Hs. repeat split.
  - apply card_two; exact Hxy.
  - apply euler_factor_2; exact Hs.
  - apply alt_euler_factor_2; exact Hs.
  - apply fock2_euler; exact Hs.
  - apply sum_over_pow2_cv0.
Qed.

Print Assumptions first_prime_zeta.
Print Assumptions whole_picture.

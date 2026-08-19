(* ================================================================= *)
(*  JensenCount.v  —  Hadamard keystone, brick 4 (step 4d core):        *)
(*  the JENSEN COUNTING INEQUALITY  n(Rr/2) . ln2 <= mean - ln|F(0)|.    *)
(*                                                                    *)
(*  For F(z) = (prod_{rho in l}(z - rho)) . G(z), G entire zero-free,   *)
(*  all zeros 0 < |rho| < Rr:                                          *)
(*                                                                    *)
(*    (#{rho in l : |rho| <= Rr/2}) . ln 2                             *)
(*        <= (1/2PI) INT_0^{2PI} ln|F(Rr e^{it})| dt  -  ln|F(0)|.      *)
(*                                                                    *)
(*  This is the heart of n(r) = O(r): each zero inside |z| <= Rr/2      *)
(*  contributes at least ln 2 to the Jensen sum                        *)
(*    sum_rho ln(Rr/|rho|) = (mean of ln|F|) - ln|F(0)|                 *)
(*  (from JensenMultiZero.jensen_multi_zero).  Bounding the RIGHT side  *)
(*  by the order-1 growth of xi then yields n(r) = O(r) -- but that     *)
(*  final step is xi-specific (XiGrowthBound) and needs xi's infinitely *)
(*  many zeros handled by a finite-radius factorization; see header of  *)
(*  the honest status below.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List.
Require Import ComplexField Cmodulus Holomorphic CPathIntegral CSegInt
        CDeriv JensenMultiZero.
Open Scope R_scope.

Lemma ln_le_loc : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq].
  - left; apply ln_increasing; assumption.
  - rewrite Heq; apply Rle_refl.
Qed.

Fixpoint count_le (r : R) (l : list C) : nat :=
  match l with
  | nil => 0%nat
  | rho :: l' => ((if Rle_lt_dec (Cmod rho) r then 1 else 0) + count_le r l')%nat
  end.

Lemma prodfac_C0_ne0 : forall l, (forall rho, In rho l -> 0 < Cmod rho) -> prodfac l C0 <> C0.
Proof.
  induction l as [| rho l' IH]; intros Hin; simpl.
  - exact C1_neq_C0.
  - apply Cmul_ne0.
    + assert (Hrne : rho <> C0).
      { intro H. pose proof (Hin rho (or_introl eq_refl)) as Hp. rewrite H in Hp.
        rewrite (proj2 (Cmod0 C0) eq_refl) in Hp. lra. }
      intro Hc. apply Hrne.
      replace rho with (Copp (Cminus C0 rho)) by ring. rewrite Hc. ring.
    + apply IH; intros r Hr; apply Hin; right; exact Hr.
Qed.

Lemma count_bound : forall Rr l, 0 < Rr ->
  (forall rho, In rho l -> 0 < Cmod rho < Rr) ->
  INR (count_le (Rr / 2) l) * ln 2 <= INR (length l) * ln Rr - ln (Cmod (prodfac l C0)).
Proof.
  intros Rr l HR; induction l as [| rho l' IH]; intros Hin.
  - simpl. rewrite Cmod_C1, ln_1. simpl. lra.
  - assert (Hrho : 0 < Cmod rho < Rr) by (apply Hin; left; reflexivity).
    assert (Hinl' : forall r, In r l' -> 0 < Cmod r < Rr) by (intros r Hr; apply Hin; right; exact Hr).
    specialize (IH Hinl').
    simpl count_le; simpl length; simpl prodfac.
    assert (Hprodne : prodfac l' C0 <> C0)
      by (apply prodfac_C0_ne0; intros r Hr; apply (proj1 (Hinl' r Hr))).
    assert (HC : Cmod (Cminus C0 rho) = Cmod rho)
      by (replace (Cminus C0 rho) with (Copp rho) by ring; apply Cmod_opp).
    rewrite Cmod_mul, HC,
      (ln_mult (Cmod rho) (Cmod (prodfac l' C0)) (proj1 Hrho) (cmod_pos _ Hprodne)).
    rewrite S_INR, plus_INR.
    assert (Hterm : INR (if Rle_lt_dec (Cmod rho) (Rr / 2) then 1 else 0)%nat * ln 2
                    <= ln Rr - ln (Cmod rho)).
    { destruct (Rle_lt_dec (Cmod rho) (Rr / 2)) as [Hle | Hgt]; simpl INR.
      - rewrite Rmult_1_l.
        assert (H2 : ln 2 + ln (Cmod rho) = ln (2 * Cmod rho))
          by (rewrite (ln_mult 2 (Cmod rho)); [ ring | lra | lra ]).
        assert (H3 : ln (2 * Cmod rho) <= ln Rr) by (apply ln_le_loc; lra). lra.
      - rewrite Rmult_0_l.
        assert (H3 : ln (Cmod rho) <= ln Rr) by (apply ln_le_loc; lra). lra. }
    rewrite Rmult_plus_distr_r. nra.
Qed.

(* the counting inequality: zeros inside |z| <= Rr/2 are bounded by the mean *)
Theorem jensen_count : forall (G Gp : C -> C) (Rr : R) (l : list C)
  (HGhol : forall z, is_Cderiv G z (Gp z))
  (HGphol : forall z, exists d, is_Cderiv Gp z d)
  (HGne0 : forall z, G z <> C0)
  (HcontG : CcontC (fun w => Cmul (Gp w) (Cinv (G w))))
  (HR : 0 < Rr)
  (Hin : forall rho, In rho l -> 0 < Cmod rho < Rr)
  (pr : Riemann_integrable
          (fun t => ln (Cmod (Cmul (prodfac l (arc Rr t)) (G (arc Rr t))))) 0 (2 * PI)),
  INR (count_le (Rr / 2) l) * ln 2
  <= RiemannInt pr / (2 * PI) - ln (Cmod (Cmul (prodfac l C0) (G C0))).
Proof.
  intros.
  assert (Hin' : forall rho, In rho l -> Cmod rho < Rr) by (intros rho Hr; apply (Hin rho Hr)).
  rewrite (jensen_multi_zero G Gp Rr HGhol HGphol HGne0 HcontG HR l Hin' pr).
  assert (Hpi : 0 < 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (Hprodne : prodfac l C0 <> C0)
    by (apply prodfac_C0_ne0; intros r Hr; apply (proj1 (Hin r Hr))).
  rewrite Cmod_mul,
    (ln_mult (Cmod (prodfac l C0)) (Cmod (G C0)) (cmod_pos _ Hprodne) (cmod_pos _ (HGne0 C0))).
  replace (2 * PI * (INR (length l) * ln Rr + ln (Cmod (G C0))) / (2 * PI))
     with (INR (length l) * ln Rr + ln (Cmod (G C0))) by (field; lra).
  pose proof (count_bound Rr l HR Hin) as Hcb. lra.
Qed.

Print Assumptions jensen_count.

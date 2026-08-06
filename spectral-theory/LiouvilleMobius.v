(* ================================================================= *)
(*  LiouvilleMobius.v  —  lambda = 1_square * mu  (pointwise).          *)
(*                                                                    *)
(*  The exact arithmetic identity underlying L <-> M (Liouville <->     *)
(*  Mertens):  sum_{d|n} lambda(d) = [n is a perfect square]           *)
(*  (lam_conv_one), equivalently (Moebius inversion)                   *)
(*    lam_eq_sq_conv_mu : lambda(n) = (1_square * mu)(n)               *)
(*                      = sum_{e^2 | n} mu(n / e^2).                    *)
(*  Proven by mult_ind (peel a prime power) + divisors_ppow_sum, using  *)
(*  the completely-multiplicative lambda (lam_mult) and a square-        *)
(*  indicator whose p^v * m multiplicativity is built here from         *)
(*  nprime_euclid (no repo square support existed).                    *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia ZArith Znumtheory Bool List.
Require Import HopfGroupTensor VonMangoldtGlobal DirichletConv DirichletMult DirichletPeel
        DirichletPPow DirichletVonMangoldtGen PrimePowerReindex LiouvilleConcrete Totient.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(*  1.  The perfect-square indicator and its p^v * m multiplicativity. *)
(* ================================================================= *)
Definition is_sq (n : nat) : bool := Nat.sqrt n * Nat.sqrt n =? n.

Lemma sq_iff : forall n, is_sq n = true <-> exists r, n = r * r.
Proof.
  intro n; unfold is_sq; split.
  - intro H; apply Nat.eqb_eq in H; exists (Nat.sqrt n); lia.
  - intros [r ->]; apply Nat.eqb_eq; rewrite Nat.sqrt_square; reflexivity.
Qed.

Lemma prime_dvd_sq : forall p r, nprime p -> Nat.divide p (r * r) -> Nat.divide p r.
Proof. intros p r Hp Hd; destruct (nprime_euclid p r r Hp Hd); assumption. Qed.

(* multiplying by p^2 does not change square-ness *)
Lemma is_sq_pp : forall p k, nprime p -> is_sq (p * p * k) = is_sq k.
Proof.
  intros p k Hp; pose proof (nprime_ge2 p Hp) as Hp2.
  destruct (is_sq k) eqn:Hk.
  - apply sq_iff in Hk as [r ->]; apply sq_iff; exists (p * r); ring.
  - destruct (is_sq (p * p * k)) eqn:Hpk; [ exfalso | reflexivity ].
    apply sq_iff in Hpk as [s Hs].
    assert (Hpd : Nat.divide p s)
      by (apply (prime_dvd_sq p s Hp); exists (p * k); rewrite <- Hs; ring).
    destruct Hpd as [t Ht].
    assert (Heq2 : p * p * k = p * p * (t * t)) by (rewrite Hs, Ht; ring).
    apply Nat.mul_cancel_l in Heq2; [ | nia ].
    assert (is_sq k = true) by (apply sq_iff; exists t; exact Heq2); congruence.
Qed.

(* p * m (with p not dividing m) is never a square *)
Lemma is_sq_p_nondvd : forall p m, nprime p -> ~ Nat.divide p m -> is_sq (p * m) = false.
Proof.
  intros p m Hp Hpm; pose proof (nprime_ge2 p Hp) as Hp2.
  destruct (is_sq (p * m)) eqn:E; [ exfalso | reflexivity ].
  apply sq_iff in E as [s Hs].
  assert (Hpd : Nat.divide p s)
    by (apply (prime_dvd_sq p s Hp); exists m; rewrite <- Hs; ring).
  destruct Hpd as [t Ht].
  apply Hpm; exists (t * t).
  assert (Heq : p * m = p * (t * t * p)) by (rewrite Hs, Ht; ring).
  apply Nat.mul_cancel_l in Heq; [ exact Heq | nia ].
Qed.

Lemma is_sq_ppow_coprime : forall p, nprime p -> forall m, ~ Nat.divide p m ->
  forall v, is_sq (p ^ v * m) = Nat.even v && is_sq m.
Proof.
  intros p Hp m Hpm v; induction v as [v IH] using (well_founded_induction lt_wf).
  destruct v as [|[|v']].
  - replace (p ^ 0 * m) with m by (simpl; ring); reflexivity.
  - simpl (Nat.even 1); rewrite andb_false_l.
    replace (p ^ 1 * m) with (p * m) by (simpl; ring).
    apply (is_sq_p_nondvd p m Hp Hpm).
  - replace (p ^ S (S v') * m) with (p * p * (p ^ v' * m)) by (simpl; ring).
    rewrite (is_sq_pp p (p ^ v' * m) Hp), (IH v' ltac:(lia)); reflexivity.
Qed.

(* ================================================================= *)
(*  2.  lambda on prime powers, and the divisor sum over p^v.          *)
(* ================================================================= *)
Definition sqind (n : nat) : Z := if is_sq n then 1 else 0.

Lemma lam_mult_pred : multiplicative lam.
Proof. split; [ exact lam_1 | intros m n Hm Hn _; apply lam_mult; assumption ]. Qed.

Lemma one_le_pow : forall b e, 1 <= b -> 1 <= b ^ e.
Proof. intros b e Hb; induction e as [|e IH]; simpl; nia. Qed.

Lemma lam_ppow : forall p j, nprime p -> lam (p ^ j) = (if Nat.even j then 1 else -1)%Z.
Proof.
  intros p j Hp; pose proof (nprime_ge2 p Hp) as Hp2.
  induction j as [|j IH]; [ reflexivity | ].
  replace (p ^ S j) with (p * p ^ j) by (simpl; ring).
  rewrite (lam_prime_step p Hp (p ^ j) (one_le_pow p j ltac:(lia))), IH.
  rewrite Nat.even_succ, <- Nat.negb_even; destruct (Nat.even j); reflexivity.
Qed.

Lemma sum_neg1 : forall v,
  sumf (seq 0 (S v)) (fun j => if Nat.even j then 1 else -1)%Z = (if Nat.even v then 1 else 0)%Z.
Proof.
  induction v as [|v IH]; [ reflexivity | ].
  rewrite List.seq_S, sumf_app, IH; cbn [sumf fold_right].
  rewrite Nat.add_0_l, Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even v); cbn; ring.
Qed.

(* the key divisor sum: sum_{d | p^v} lambda(d) = [v even] *)
Lemma lam_ppow_conv : forall p v, nprime p ->
  dconv lam done (p ^ v) = (if Nat.even v then 1 else 0)%Z.
Proof.
  intros p v Hp; pose proof (nprime_ge2 p Hp) as Hp2.
  assert (Hzp : prime (Z.of_nat p)) by (destruct (nprime_iff_Zprime p) as [Hf _]; exact (Hf Hp)).
  rewrite (dconv_as_div lam done (p ^ v) (one_le_pow p v ltac:(lia))).
  rewrite (sumf_ext (divisors (p ^ v)) _ lam) by (intros d _; unfold done; cbn beta; ring).
  rewrite (divisors_ppow_sum p v lam Hzp).
  rewrite (sumf_ext (seq 0 (S v)) (fun j => lam (p ^ j))
             (fun j => if Nat.even j then 1 else -1)%Z) by (intros j _; apply lam_ppow; exact Hp).
  apply sum_neg1.
Qed.

(* ================================================================= *)
(*  3.  sum_{d|n} lambda(d) = [n square], then Moebius inversion.      *)
(* ================================================================= *)
Theorem lam_conv_one : forall n, 1 <= n -> dconv lam done n = sqind n.
Proof.
  apply (mult_ind (fun n => dconv lam done n = sqind n)).
  - vm_compute; reflexivity.
  - intros p v m Hzp Hpm Hv Hm IH.
    assert (Hp : nprime p) by (destruct (nprime_iff_Zprime p) as [_ Hb]; exact (Hb Hzp)).
    pose proof (nprime_ge2 p Hp) as Hp2.
    destruct (dconv_mult lam done lam_mult_pred done_mult) as [_ Hmul].
    rewrite (Hmul (p ^ v) m (one_le_pow p v ltac:(lia)) Hm (gcd_ppow_coprime p v m Hzp Hpm)).
    rewrite (lam_ppow_conv p v Hp), IH; unfold sqind.
    rewrite (is_sq_ppow_coprime p Hp m Hpm v).
    destruct (Nat.even v), (is_sq m); reflexivity.
Qed.

(* lambda = 1_square * mu  (pointwise):  lambda(n) = sum_{e^2 | n} mu(n/e^2). *)
Theorem lam_eq_sq_conv_mu : forall n, 1 <= n -> lam n = dconv sqind mu n.
Proof.
  apply (mobius_inversion lam sqind).
  intros n Hn; symmetry; exact (lam_conv_one n Hn).
Qed.

Print Assumptions lam_conv_one.
Print Assumptions lam_eq_sq_conv_mu.

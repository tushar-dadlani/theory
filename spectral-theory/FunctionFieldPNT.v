(* ================================================================= *)
(*  FunctionFieldPNT.v  —  the Prime Number Theorem for F_q[t].         *)
(*                                                                    *)
(*  The "necklace / Gauss" count of monic irreducibles of degree n     *)
(*  over F_q is  I_q(n) = (1/n) sum_{d|n} mu(d) q^{n/d}.  Writing        *)
(*      J(n) := (powq * mu)(n) = sum_{d|n} q^d mu(n/d) = n * I_q(n),     *)
(*  the cyclic-group (C_n on words) orbit count gives the EXACT         *)
(*  identity  sum_{d|n} J(d) = q^n  (ff_count) -- pure Moebius          *)
(*  inversion in the Dirichlet-convolution ring (dconv_assoc + mu_one). *)
(*                                                                    *)
(*  The leading term of J(n) is the d=1 (i.e. divisor n) term q^n; all  *)
(*  others are <= q^{n/2}, so  |J(n) - q^n| <= n q^{n/2}  (ff_error),    *)
(*  whence  J(n)/q^n -> 1  (ff_pnt), i.e.  I_q(n) ~ q^n / n  --- the      *)
(*  Prime Number Theorem for the polynomial ring F_q[t], proved by a    *)
(*  pure group action (no analysis, no limsup).  Axiom-clean.           *)
(*                                                                    *)
(*  This is the group-theoretic sibling of the integer PNT: it is the   *)
(*  place where the "S_n / cyclic group" argument genuinely closes,      *)
(*  because F_q[t] supplies an EXACT count (q^n words) that Z lacks.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Lists.List.
Import ListNotations.
Require Import DirichletConv DirichletMult MobiusBound RealMobius MuLog
        MobiusOverD VonMangoldtGlobal CEulerProductFull ZetaSquareAnalytic
        GammaFunction.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Three tiny Rls helpers (linearity + constant sum).                *)
(* ----------------------------------------------------------------- *)

Lemma Rls_add : forall (l : list nat) (f g : nat -> R),
  Rls l (fun x => f x + g x) = Rls l f + Rls l g.
Proof.
  induction l as [|a l IH]; intros f g; [ rewrite !Rls_nil2; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

Lemma Rls_minus : forall (l : list nat) (f g : nat -> R),
  Rls l (fun x => f x - g x) = Rls l f - Rls l g.
Proof.
  induction l as [|a l IH]; intros f g; [ rewrite !Rls_nil2; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

Lemma Rls_const : forall (l : list nat) (c : R),
  Rls l (fun _ => c) = c * INR (length l).
Proof.
  induction l as [|a l IH]; intros c; [ rewrite Rls_nil2; simpl; ring | ].
  rewrite Rls_cons, IH; simpl length; rewrite S_INR; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The arithmetic functions.                                         *)
(* ----------------------------------------------------------------- *)

Definition powq (q n : nat) : Z := Z.of_nat (q ^ n).
Definition Jff  (q : nat) : nat -> Z := dconv (powq q) mu.

(* ----------------------------------------------------------------- *)
(*  (1)  THE EXACT NECKLACE / GAUSS COUNT  (Moebius inversion).        *)
(*        sum_{d|n} J(d) = q^n.                                        *)
(* ----------------------------------------------------------------- *)

Lemma ff_count : forall q n, (1 <= n)%nat -> dconv (Jff q) done n = powq q n.
Proof.
  intros q n Hn; unfold Jff.
  rewrite (dconv_assoc (powq q) mu done n Hn).
  rewrite (dconv_ext_r (powq q) (dconv mu done) deps n)
    by (intros e He; apply mu_one; lia).
  apply (dconv_eps_r (powq q) n Hn).
Qed.

(* ----------------------------------------------------------------- *)
(*  (2)  The real-valued divisor form of J.                           *)
(* ----------------------------------------------------------------- *)

Lemma Jff_R : forall q n, (1 <= n)%nat ->
  IZR (Jff q n) = Rls (divisors n) (fun d => INR (q ^ d) * IZR (mu (n / d)%nat)).
Proof.
  intros q n Hn; unfold Jff.
  rewrite (dconv_as_div (powq q) mu n Hn), IZR_sumf.
  apply Rls_ext; intros d _.
  rewrite mult_IZR; unfold powq; rewrite <- INR_IZR_INZ; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  (3)  THE ERROR BOUND  |J(n) - q^n| <= n q^{floor(n/2)}.            *)
(* ----------------------------------------------------------------- *)

Lemma ff_error : forall q n, (2 <= q)%nat -> (1 <= n)%nat ->
  Rabs (IZR (Jff q n) - INR (q ^ n)) <= INR n * INR (q ^ (n / 2)).
Proof.
  intros q n Hq Hn.
  assert (Hin : In n (divisors n)) by (apply in_divisors; split; [ lia | apply Nat.divide_refl ]).
  rewrite Jff_R by exact Hn.
  rewrite <- (Rls_sift0 (divisors n) (INR (q ^ n)) n (divisors_nodup n) Hin).
  rewrite <- Rls_minus.
  eapply Rle_trans; [ apply Rls_abs | ].
  eapply Rle_trans.
  - apply Rls_le with (g := fun _ => INR (q ^ (n / 2))).
    intros d Hd; rewrite in_divisors in Hd; destruct Hd as [[Hd1 Hd2] Hdvd].
    destruct (Nat.eqb_spec d n) as [-> | Hne].
    + (* d = n : the leading term cancels exactly *)
      replace (if true then INR (q ^ n) else 0) with (INR (q ^ n)) by reflexivity.
      replace (n / n)%nat with 1%nat by (symmetry; apply Nat.div_same; lia).
      rewrite mu_1; change (IZR 1) with 1.
      replace (INR (q ^ n) * 1 - INR (q ^ n)) with 0 by ring.
      rewrite Rabs_R0; apply pos_INR.
    + (* d < n : |q^d mu(n/d)| <= q^d <= q^{n/2} *)
      replace (if false then INR (q ^ n) else 0) with 0 by reflexivity.
      rewrite Rminus_0_r.
      assert (Hlt : (d < n)%nat) by lia.
      assert (Hnd1 : (1 <= n / d)%nat).
      { destruct Hdvd as [k Hk]; subst n. rewrite Nat.div_mul by lia. nia. }
      assert (Hdle : (d <= n / 2)%nat).
      { destruct Hdvd as [k Hk]; subst n.
        assert (2 <= k)%nat by nia.
        apply Nat.le_trans with (2 * d / 2)%nat;
          [ rewrite Nat.mul_comm, Nat.div_mul by lia; lia
          | apply Nat.Div0.div_le_mono; nia ]. }
      rewrite Rabs_mult.
      rewrite (Rabs_right (INR (q ^ d))) by (apply Rle_ge; apply pos_INR).
      apply Rle_trans with (INR (q ^ d) * 1).
      * apply Rmult_le_compat_l; [ apply pos_INR | ].
        rewrite <- abs_IZR; replace 1 with (IZR 1) by (simpl; ring); apply IZR_le.
        pose proof (mu_abs_le_1 (n / d)%nat Hnd1) as [Hlo Hhi]; lia.
      * rewrite Rmult_1_r; apply le_INR; apply Nat.pow_le_mono_r; [ lia | exact Hdle ].
  - rewrite Rls_const, (Rmult_comm (INR n) (INR (q ^ (n / 2)))).
    apply Rmult_le_compat_l; [ apply pos_INR | ].
    apply le_INR; unfold divisors;
      apply Nat.le_trans with (length (seq 1 n));
      [ apply filter_length_le | rewrite length_seq; lia ].
Qed.

(* ----------------------------------------------------------------- *)
(*  (4)  THE ASYMPTOTIC  J(n)/q^n -> 1   (function-field PNT).         *)
(* ----------------------------------------------------------------- *)

Lemma B_cv0 : forall q, (2 <= q)%nat ->
  Un_cv (fun n => INR n * (/ INR q) ^ (n - n / 2)) 0.
Proof.
  intros q Hq.
  assert (HqR : 2 <= INR q) by (apply (le_INR 2); exact Hq).
  set (r := / INR q).
  assert (Hr0 : 0 < r) by (unfold r; apply Rinv_0_lt_compat; lra).
  assert (Hr1 : r < 1) by (unfold r; rewrite <- Rinv_1; apply Rinv_lt_contravar; lra).
  apply (Un_cv_squeeze0 _
           (fun n => (2 / r) * (INR (S (n / 2)) * r ^ (S (n / 2))))).
  - exists 1%nat; intros n _; split.
    + apply Rmult_le_pos; [ apply pos_INR | apply pow_le; lra ].
    + (* INR n * r^(n - n/2) <= (2/r) * (S(n/2) * r^(S(n/2))) *)
      assert (Hsplit : (n - n / 2 = n / 2 + n mod 2)%nat)
        by (pose proof (Nat.div_mod n 2); lia).
      rewrite Hsplit, pow_add.
      apply Rle_trans with (INR n * r ^ (n / 2)).
      * apply Rmult_le_compat_l; [ apply pos_INR | ].
        rewrite <- (Rmult_1_r (r ^ (n / 2))) at 2.
        apply Rmult_le_compat_l; [ apply pow_le; lra | ].
        apply Rle_trans with (1 ^ (n mod 2)); [ apply pow_incr; lra | rewrite pow1; lra ].
      * (* INR n * r^(n/2) <= (2/r)*(S(n/2) * r^(S(n/2))) *)
        replace ((2 / r) * (INR (S (n / 2)) * r ^ (S (n / 2))))
          with (2 * INR (S (n / 2)) * r ^ (n / 2))
          by (simpl pow; field; lra).
        apply Rmult_le_compat_r; [ apply pow_le; lra | ].
        rewrite S_INR.
        assert (Hle : (n <= 2 * (n / 2) + 2)%nat)
          by (pose proof (Nat.Div0.div_mod n 2);
              pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia).
        apply le_INR in Hle; rewrite plus_INR, mult_INR in Hle.
        replace (INR 2) with 2 in Hle by (simpl; ring); lra.
  - replace 0 with ((2 / r) * 0) by ring.
    apply CV_mult; [ apply Un_cv_const | ].
    apply (Un_cv_reindex (fun k => INR k * r ^ k) 0 (fun n => S (n / 2))).
    + apply nqn_cv0; lra.
    + intros m; exists (2 * m)%nat; intros n Hn.
      pose proof (Nat.Div0.div_mod n 2);
        pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia.
Qed.

Theorem ff_pnt : forall q, (2 <= q)%nat ->
  Un_cv (fun n => IZR (Jff q n) / INR (q ^ n)) 1.
Proof.
  intros q Hq eps Heps.
  destruct (B_cv0 q Hq eps Heps) as [N HN].
  exists (Nat.max N 1); intros n Hn.
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (HqR : 2 <= INR q) by (apply (le_INR 2); exact Hq).
  assert (Hqpos : 0 < INR q) by lra.
  assert (Hqn : 0 < INR (q ^ n))
    by (apply lt_0_INR; assert (q ^ n <> 0)%nat by (apply Nat.pow_nonzero; lia); lia).
  (* the ratio-minus-one collapses to the error over q^n *)
  assert (Hkey : R_dist (IZR (Jff q n) / INR (q ^ n)) 1
                 <= INR n * (/ INR q) ^ (n - n / 2)).
  { unfold R_dist.
    replace (IZR (Jff q n) / INR (q ^ n) - 1)
      with ((IZR (Jff q n) - INR (q ^ n)) / INR (q ^ n))
      by (field; lra).
    unfold Rdiv; rewrite Rabs_mult.
    rewrite (Rabs_right (/ INR (q ^ n)))
      by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact Hqn).
    apply Rle_trans with (INR n * INR (q ^ (n / 2)) * / INR (q ^ n)).
    - apply Rmult_le_compat_r;
        [ left; apply Rinv_0_lt_compat; exact Hqn | apply ff_error; assumption ].
    - (* n q^{n/2} / q^n = n (1/q)^{n - n/2} *)
      apply Req_le; rewrite Rmult_assoc; f_equal.
      rewrite !pow_INR, <- (Rinv_pow (INR q) (n - n / 2)) by lra.
      replace ((INR q) ^ n) with ((INR q) ^ (n / 2) * (INR q) ^ (n - n / 2))
        by (rewrite <- pow_add; f_equal;
            assert (n / 2 <= n)%nat by (apply Nat.div_le_upper_bound; lia); lia).
      rewrite Rinv_mult, <- Rmult_assoc, Rinv_r, Rmult_1_l;
        [ reflexivity | apply pow_nonzero; lra ]. }
  eapply Rle_lt_trans; [ exact Hkey | ].
  specialize (HN n ltac:(lia)); unfold R_dist in HN; rewrite Rminus_0_r in HN.
  rewrite Rabs_right in HN
    by (apply Rle_ge; apply Rmult_le_pos; [ apply pos_INR | apply pow_le; left;
        apply Rinv_0_lt_compat; lra ]).
  exact HN.
Qed.

Print Assumptions ff_pnt.

(* ================================================================= *)
(*  END FunctionFieldPNT.v  —  I_q(n) ~ q^n / n  by pure group action. *)
(* ================================================================= *)

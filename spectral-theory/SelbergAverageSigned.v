(* ================================================================= *)
(*  SelbergAverageSigned.v  —  RUNG 3c-B1: the signed Selberg symmetry. *)
(*                                                                    *)
(*  The SIGNED companion of SelbergAverage.  With Vsig n := Rem n / n   *)
(*  (so Vrem n = |Vsig n|), dividing the signed Selberg inequality      *)
(*      |Rform N| <= C*N,   Rform N = Rem N ln N + Sum Lam(d) Rem(N/d)  *)
(*  by N and reindexing to the Lam(d)/d weights gives                   *)
(*                                                                    *)
(*    selberg_average_signed :                                         *)
(*      |Vsig N * ln N + Sum_{d<=N} (Lam d/d) Vsig(N/d)|  <=  C'.        *)
(*                                                                    *)
(*  Unlike the |.|-version, signs forbid the clean INR(N/d) <= N/d       *)
(*  bound, so the reindex introduces a difference term; it is O(1),      *)
(*  bounded by (Kup-1)*psi(N)/N <= (Kup-1)*Kup (frac_diff_bound +        *)
(*  psi_upper).  This is the Selberg symmetry the cancellation core       *)
(*  (Rung 3c-B3) plays against the |.|-inequality (3a).  Axiom-clean.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        MobiusOverD SelbergEndgame SelbergRForm SelbergPsiForm.
Open Scope R_scope.

Definition Vsig (n : nat) : R := Rem n / INR n.

Lemma Rls_minus' : forall (l : list nat) (f g : nat -> R),
  Rls l (fun x => f x - g x) = Rls l f - Rls l g.
Proof.
  induction l as [|a l IH]; intros f g; [ rewrite !Rls_nil2; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

Lemma Rls_scal_r : forall (l : list nat) (f : nat -> R) (c : R),
  Rls l (fun x => f x * c) = Rls l f * c.
Proof.
  induction l as [|a l IH]; intros f c; [ rewrite !Rls_nil2; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

(* The per-term reindex defect: replacing 1/N by 1/(d*(N/d)) costs O(Lam d / N). *)
Lemma frac_diff_bound : forall N d, (1 <= d <= N)%nat ->
  Rabs (Lam d / INR d * Vsig (N / d)%nat - / INR N * (Lam d * Rem (N / d)%nat))
  <= Lam d * ((Kup - 1) * / INR N).
Proof.
  intros N d [Hd1 HdN].
  assert (HK1 : 0 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  assert (Hdpos : 0 < INR d) by (apply lt_0_INR; lia).
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  set (m := (N / d)%nat).
  assert (Hm1 : (1 <= m)%nat).
  { unfold m; pose proof (Nat.Div0.div_mod N d);
      pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia. }
  assert (Hmpos : 0 < INR m) by (apply lt_0_INR; lia).
  assert (Hdm : INR d * INR m <= INR N).
  { unfold m; rewrite <- mult_INR; apply le_INR;
      pose proof (Nat.Div0.div_mod N d); nia. }
  assert (HNle : INR N <= INR m * INR d + INR d).
  { unfold m; rewrite <- mult_INR, <- plus_INR; apply le_INR;
      pose proof (Nat.Div0.div_mod N d);
      pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia. }
  assert (Hbr : 0 <= / (INR d * INR m) - / INR N).
  { pose proof (Rinv_le_contravar (INR d * INR m) (INR N)
                 (Rmult_lt_0_compat _ _ Hdpos Hmpos) Hdm); lra. }
  assert (Hfrac : INR m * (/ (INR d * INR m) - / INR N) <= / INR N).
  { replace (INR m * (/ (INR d * INR m) - / INR N)) with (/ INR d - INR m * / INR N)
      by (field; split; lra).
    apply Rmult_le_reg_r with (INR d * INR N);
      [ apply Rmult_lt_0_compat; assumption | ].
    replace ((/ INR d - INR m * / INR N) * (INR d * INR N)) with (INR N - INR m * INR d)
      by (field; split; lra).
    replace (/ INR N * (INR d * INR N)) with (INR d) by (field; lra).
    lra. }
  replace (Lam d / INR d * Vsig m - / INR N * (Lam d * Rem m))
    with (Lam d * Rem m * (/ (INR d * INR m) - / INR N))
    by (unfold Vsig; field; split; lra).
  rewrite Rabs_mult, (Rabs_right (/ (INR d * INR m) - / INR N)) by (apply Rle_ge; exact Hbr).
  rewrite Rabs_mult, (Rabs_right (Lam d)) by (apply Rle_ge; apply Lam_nonneg).
  apply Rle_trans with (Lam d * ((Kup - 1) * INR m) * (/ (INR d * INR m) - / INR N)).
  { apply Rmult_le_compat_r; [ exact Hbr | ].
    apply Rmult_le_compat_l; [ apply Lam_nonneg | apply Rem_bound ]. }
  replace (Lam d * ((Kup - 1) * INR m) * (/ (INR d * INR m) - / INR N))
    with (Lam d * ((Kup - 1) * (INR m * (/ (INR d * INR m) - / INR N)))) by ring.
  apply Rmult_le_compat_l; [ apply Lam_nonneg | ].
  apply Rmult_le_compat_l; [ exact HK1 | exact Hfrac ].
Qed.

Theorem selberg_average_signed : forall N, (1 <= N)%nat ->
  Rabs (Vsig N * ln (INR N)
        + Rls (seq 1 N) (fun d => Lam d / INR d * Vsig (N / d)%nat))
  <= (88 + 3 * Kup + 1) + (Kup - 1) * Kup.
Proof.
  intros N HN.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (HNne : INR N <> 0) by lra.
  assert (HK1 : 0 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  set (G := Rls (seq 1 N) (fun d => Lam d / INR d * Vsig (N / d)%nat)).
  set (S := Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat)).
  assert (Hrf : Rform N * / INR N = Vsig N * ln (INR N) + S * / INR N)
    by (unfold Rform, Vsig, S; field; exact HNne).
  replace (Vsig N * ln (INR N) + G) with (Rform N * / INR N + (G - S * / INR N))
    by (rewrite Hrf; ring).
  eapply Rle_trans; [ apply Rabs_triang | apply Rplus_le_compat ].
  - rewrite Rabs_mult, (Rabs_right (/ INR N))
      by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact HNpos).
    apply Rmult_le_reg_r with (INR N); [ exact HNpos | ].
    rewrite Rmult_assoc.
    rewrite Rinv_l by exact HNne.
    rewrite Rmult_1_r; apply (selberg_inequality N HN).
  - unfold G, S.
    rewrite (Rmult_comm (Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat)) (/ INR N)).
    rewrite Rls_scal, <- Rls_minus'.
    eapply Rle_trans; [ apply Rls_abs | ].
    eapply Rle_trans.
    + apply Rls_le with (g := fun d => Lam d * ((Kup - 1) * / INR N)).
      intros d Hd; rewrite in_seq in Hd; apply frac_diff_bound; lia.
    + rewrite Rls_scal_r.
      change (Rls (seq 1 N) Lam) with (psi N).
      apply Rle_trans with (INR N * Kup * ((Kup - 1) * / INR N)).
      * apply Rmult_le_compat_r;
          [ apply Rmult_le_pos; [ exact HK1 | left; apply Rinv_0_lt_compat; exact HNpos ]
          | apply psi_upper ].
      * apply Req_le; field; exact HNne.
Qed.

Print Assumptions selberg_average_signed.

(* ================================================================= *)
(*  END SelbergAverageSigned.v  —  RUNG 3c-B1: signed Selberg symmetry. *)
(* ================================================================= *)

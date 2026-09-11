(* ================================================================= *)
(*  CLPhiUniform.v  --  one K and one del for ALL non-principal chi.  *)
(*                                                                    *)
(*  CLPhiBounded.Phi_bounded produces K and del PER character.  The    *)
(*  endgame sums over all p-1 characters at once, so it needs a single *)
(*  pair valid for every non-principal a simultaneously.  Since there  *)
(*  are finitely many, that is a max/min over a range -- but it has to *)
(*  be done as an induction, because the existentials are nested       *)
(*  inside the quantifier over a.                                      *)
(*                                                                    *)
(*  The induction runs over an upper cutoff B <= p-1 and is stated so  *)
(*  that the step only ever needs Phi_bounded at the single index B,   *)
(*  and only when 0 < B < p-1 -- outside that range no admissible a    *)
(*  equals B, so the step can take K = 0, del = 1 there.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus CSeries RootsOfUnity ZmodOrder
        DirichletModP CTwistedCoeff CLSeries CVonMangoldtChi CLPhiBounded.
Open Scope R_scope.

Section Uniform.

Variable p g : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.

Lemma Phi_bounded_upto : forall B, (B <= p - 1)%nat ->
  exists K del, 0 < del /\
    forall A, (0 < A < p - 1)%nat -> (A < B)%nat ->
    forall sig (Hs : 1 < Re (sc sig)), sig < 1 + del ->
      Cmod (Phichi p g A Hg Hord (sc sig) Hs) <= K.
Proof.
  induction B as [| B IH]; intro HB.
  - exists 0, 1. split; [ lra | ]. intros A HA Hlt. lia.
  - destruct (IH ltac:(lia)) as [K1 [del1 [Hd1 H1]]].
    assert (Hcase : exists K2 del2, 0 < del2 /\
              ((0 < B < p - 1)%nat ->
                 forall sig (Hs : 1 < Re (sc sig)), sig < 1 + del2 ->
                   Cmod (Phichi p g B Hg Hord (sc sig) Hs) <= K2)).
    { destruct (lt_dec 0 B) as [Hb0 | Hb0].
      - destruct (lt_dec B (p - 1)) as [Hb1 | Hb1].
        + destruct (Phi_bounded p g B Hp Hg Hord (conj Hb0 Hb1))
            as [K2 [del2 [Hd2 H2]]].
          exists K2, del2. split; [ exact Hd2 | ]. intros _. exact H2.
        + exists 0, 1. split; [ lra | ]. intros Hc. lia.
      - exists 0, 1. split; [ lra | ]. intros Hc. lia. }
    destruct Hcase as [K2 [del2 [Hd2 H2]]].
    exists (Rmax K1 K2), (Rmin del1 del2). split.
    { apply Rmin_pos; assumption. }
    intros A HA Hlt sig Hs Hsig.
    destruct (Nat.eq_dec A B) as [E | E].
    + subst A.
      eapply Rle_trans; [ | apply Rmax_r ].
      apply H2; [ exact HA | ].
      eapply Rlt_le_trans; [ exact Hsig | ].
      apply Rplus_le_compat_l, Rmin_r.
    + eapply Rle_trans; [ | apply Rmax_l ].
      apply H1; [ exact HA | lia | ].
      eapply Rlt_le_trans; [ exact Hsig | ].
      apply Rplus_le_compat_l, Rmin_l.
Qed.

Theorem Phi_bounded_uniform : exists K del, 0 < del /\
  forall A, (0 < A < p - 1)%nat ->
  forall sig (Hs : 1 < Re (sc sig)), sig < 1 + del ->
    Cmod (Phichi p g A Hg Hord (sc sig) Hs) <= K.
Proof.
  destruct (Phi_bounded_upto (p - 1) ltac:(lia)) as [K [del [Hd H]]].
  exists K, del. split; [ exact Hd | ].
  intros A HA sig Hs Hsig. apply H; [ exact HA | lia | exact Hsig ].
Qed.

End Uniform.

Print Assumptions Phi_bounded_uniform.

(* ================================================================= *)
(*  END CLPhiUniform.v                                                *)
(* ================================================================= *)

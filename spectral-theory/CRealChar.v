(* ================================================================= *)
(*  CRealChar.v  --  the quadratic character as a Z-valued function.  *)
(*                                                                    *)
(*  Toward L(1,chi) <> 0 for REAL chi -- the case where 3-4-1          *)
(*  degenerates (chi^2 = chi_0 makes the third factor acquire the      *)
(*  pole) and the elementary hyperbola argument is needed instead:     *)
(*                                                                    *)
(*      f = 1 * chi,  f >= 0,  f(m^2) >= 1,                            *)
(*      so sum_{n<=x} f(n)/sqrt n >= sum_{m<=sqrt x} 1/m -> infinity,  *)
(*      while L(1,chi) = 0 would force that sum bounded.               *)
(*                                                                    *)
(*  The whole positivity half of that is arithmetic, not analysis, and *)
(*  the repo's Dirichlet-convolution ring is Z-valued.  So the first   *)
(*  move is to leave C: a real character takes values in {-1,0,1}, so  *)
(*  it is a Z-valued function, and then DirichletMult.dconv_mult and   *)
(*  DirichletPeel.mult_ind apply directly.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus RootsOfUnity ZmodOrder DirichletModP
        DirichletLEuler CharModulus ZetaFn DirichletConv DirichletMult.
Import ListNotations.
Open Scope R_scope.

Section RealChar.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis Hreal : forall n, Cconj (dchar p g A n) = dchar p g A n.

Lemma Hp2 : (2 <= p)%nat.
Proof. destruct Hp; lia. Qed.

(* a real character takes only the values 0, 1, -1 *)
Lemma dchar_pm1 : forall n, (n mod p =? 0)%nat = false ->
  dchar p g A n = C1 \/ dchar p g A n = Copp C1.
Proof.
  intros n Hn.
  pose proof (Hreal n) as Hr.
  assert (Him : Im (dchar p g A n) = 0).
  { apply (f_equal Im) in Hr. unfold Cconj in Hr; cbn [Im] in Hr. lra. }
  pose proof (Cmod_dchar_1 p g A n Hn) as Hm.
  assert (Hsq : Re (dchar p g A n) * Re (dchar p g A n) = 1).
  { unfold Cmod, Cnorm2 in Hm. rewrite Him in Hm.
    assert (H0 : 0 <= Re (dchar p g A n) * Re (dchar p g A n) + 0 * 0).
    { pose proof (Rle_0_sqr (Re (dchar p g A n))) as Hsq0.
      unfold Rsqr in Hsq0. lra. }
    pose proof (sqrt_sqrt _ H0) as Hss.
    rewrite Hm in Hss. lra. }
  assert (Hfac : (Re (dchar p g A n) - 1) * (Re (dchar p g A n) + 1) = 0) by nra.
  destruct (Rmult_integral _ _ Hfac) as [E | E].
  - left. apply Ceq; unfold C1; cbn [Re Im]; [ lra | rewrite Him; reflexivity ].
  - right. apply Ceq; unfold Copp, C1; cbn [Re Im]; [ lra | rewrite Him; ring ].
Qed.

(* the Z-valued avatar *)
Definition chz (n : nat) : Z :=
  if (n mod p =? 0)%nat then 0
  else if Ceq_dec2 (dchar p g A n) C1 then 1 else -1.

Lemma chz_spec : forall n, RtoC (IZR (chz n)) = dchar p g A n.
Proof.
  intro n. unfold chz.
  destruct (n mod p =? 0)%nat eqn:E.
  - assert (Hd : Nat.divide p n).
    { apply (proj1 (Nat.Lcm0.mod_divide n p)). apply Nat.eqb_eq; exact E. }
    rewrite (dchar_zero p g A n Hd).
    unfold RtoC, C0; apply Ceq; cbn; ring.
  - destruct (Ceq_dec2 (dchar p g A n) C1) as [Heq | Hne].
    + rewrite Heq. unfold RtoC, C1; apply Ceq; cbn; ring.
    + destruct (dchar_pm1 n E) as [H1 | H1]; [ contradiction | ].
      rewrite H1. unfold RtoC, Copp, C1; apply Ceq; cbn; ring.
Qed.

Lemma chz_values : forall n, chz n = 0%Z \/ chz n = 1%Z \/ chz n = (-1)%Z.
Proof.
  intro n. unfold chz. destruct (n mod p =? 0)%nat; [ left; reflexivity | ].
  destruct (Ceq_dec2 (dchar p g A n) C1); [ right; left | right; right ]; reflexivity.
Qed.

Lemma chz_abs_le1 : forall n, (Z.abs (chz n) <= 1)%Z.
Proof. intro n. destruct (chz_values n) as [E | [E | E]]; rewrite E; lia. Qed.

(* injectivity of RtoC o IZR, to transfer identities back from C *)
Lemma IZR_RtoC_inj : forall a b : Z, RtoC (IZR a) = RtoC (IZR b) -> a = b.
Proof.
  intros a b H. apply (f_equal Re) in H. unfold RtoC in H; cbn [Re] in H.
  apply eq_IZR. exact H.
Qed.

(* chz is completely multiplicative, hence multiplicative *)
Lemma chz_mul : forall m n, chz (m * n)%nat = (chz m * chz n)%Z.
Proof.
  intros m n. apply IZR_RtoC_inj.
  rewrite mult_IZR.
  assert (E : RtoC (IZR (chz m) * IZR (chz n))
              = Cmul (RtoC (IZR (chz m))) (RtoC (IZR (chz n))))
    by (unfold RtoC; apply Ceq; cbn; ring).
  rewrite E, !chz_spec.
  rewrite (dchar_mul p g A m n Hp Hg Hord). reflexivity.
Qed.

Lemma chz_one : chz 1%nat = 1%Z.
Proof.
  apply IZR_RtoC_inj. rewrite chz_spec, (dchar_1 p g A Hp Hg Hord).
  unfold RtoC, C1; apply Ceq; cbn; ring.
Qed.

Theorem chz_mult : multiplicative chz.
Proof.
  split; [ exact chz_one | ].
  intros m n _ _ _. apply chz_mul.
Qed.

(* ----------------------------------------------------------------- *)
(*  f = 1 * chi, and its multiplicativity                              *)
(* ----------------------------------------------------------------- *)

Definition fchi : nat -> Z := dconv done chz.

Theorem fchi_mult : multiplicative fchi.
Proof. apply dconv_mult; [ apply done_mult | apply chz_mult ]. Qed.

End RealChar.

Print Assumptions chz_mult.
Print Assumptions fchi_mult.

(* ================================================================= *)
(*  END CRealChar.v                                                   *)
(* ================================================================= *)

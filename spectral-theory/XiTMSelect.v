(* ================================================================= *)
(*  XiTMSelect.v  —  the glue, part 2: choosing the truncation.        *)
(*                                                                    *)
(*    Msel : R -> nat, a FUNCTION giving, for each radius r, a         *)
(*      truncation index M with the tail product zero-free on          *)
(*      Cmod z < r.                                                    *)
(*                                                                    *)
(*  The local theorem got its M by destructing an existential inside a *)
(*  proof.  That is fine for one disk and useless for gluing: to build *)
(*  a single H on all of C the index must be a function of the point,  *)
(*  and functions do not come out of Props.                            *)
(*                                                                    *)
(*  No new axiom is needed, because the search is over nat and the     *)
(*  test is a comparison of reals, which is already decidable here:    *)
(*  sig_forall_dec (an axiom this development ALREADY carries, and     *)
(*  which the classical reals themselves are built on) turns           *)
(*  "not every n fails" into an n.  Rle_dec supplies the decision.     *)
(*  So Msel is data at no cost -- unlike `choice`, which would be      *)
(*  needed to pick the cofactor family Gseq, and which we still        *)
(*  decline (ZeroEnumG takes Gseq as given instead).                   *)
(*                                                                    *)
(*  TM_ne0_disk isolates the estimate the local proof did inline: if   *)
(*  KR r . Ttl M stays below u0 = min (1, 1/2e) then exp of it is      *)
(*  within 1/2 of 1, tail_prod_ge keeps every partial tail product     *)
(*  above 1/2, and the limit inherits it.  u0 is chosen so that        *)
(*  exp_m1_le closes with exp 1 symbolic -- no numeric bound on e.     *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        CSeries CInfProd JensenMultiZero CZeroListFactor
        RiemannXiEntire XiZeroEnum XiHadamardProd XiHadamardUnif
        XiProdLimit XiTailProd XiTMHolo.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  a selector for nat, from a decidable real test                 *)
(* ----------------------------------------------------------------- *)
Definition natsel (f : nat -> R) (e : R) : nat :=
  match ClassicalDedekindReals.sig_forall_dec (fun n => e <= f n)
          (fun n => Rle_dec e (f n)) with
  | inleft (exist _ n _) => n
  | inright _ => O
  end.

Lemma natsel_spec : forall f e, (exists n, f n < e) -> f (natsel f e) < e.
Proof.
  intros f e Hex. unfold natsel.
  destruct (ClassicalDedekindReals.sig_forall_dec (fun n => e <= f n)
              (fun n => Rle_dec e (f n))) as [[n Hn] | Hall];
    [ lra | destruct Hex as [n Hn]; specialize (Hall n); lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the smallness threshold                                        *)
(* ----------------------------------------------------------------- *)
Definition u0 : R := Rmin 1 (/ (2 * exp 1)).

Lemma u0_pos : 0 < u0.
Proof.
  pose proof (exp_pos 1). unfold u0.
  apply Rmin_glb_lt; [ lra | apply Rinv_0_lt_compat; lra ].
Qed.

Lemma KR_pos : forall r, 0 < r -> 0 < KR r.
Proof.
  intros r Hr. unfold KR. pose proof (exp_pos r) as HeR.
  apply Rmult_lt_0_compat; [ nra | ].
  assert (0 < 3 * (1 + r) * exp r) by (apply Rmult_lt_0_compat; nra). lra.
Qed.

Lemma exp_half : forall u, 0 <= u -> u < u0 -> exp u - 1 <= / 2.
Proof.
  intros u Hu Hlt. pose proof (exp_pos 1) as Hp1.
  assert (H1 : u <= 1) by (pose proof (Rmin_l 1 (/ (2 * exp 1))); unfold u0 in Hlt; lra).
  assert (H2 : u < / (2 * exp 1))
    by (pose proof (Rmin_r 1 (/ (2 * exp 1))); unfold u0 in Hlt; lra).
  pose proof (exp_m1_le u Hu) as He.
  assert (Hexp1 : exp u <= exp 1) by (apply exp_le; exact H1).
  assert (Hs1 : u * exp u <= u * exp 1) by (apply Rmult_le_compat_l; lra).
  assert (Hs2 : u * exp 1 <= / (2 * exp 1) * exp 1)
    by (apply Rmult_le_compat_r; lra).
  assert (Hkey : / (2 * exp 1) * exp 1 = / 2) by (field; lra).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the tail product is zero-free once the tail sum is small       *)
(* ----------------------------------------------------------------- *)
Section Select.

Variable rho : nat -> C.
Hypothesis Henum : ZeroEnum rho.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Theorem TM_ne0_disk : forall r, 0 < r ->
  forall M, KR r * Ttl rho Henum Hlow M < u0 ->
  forall z, Cmod z < r -> TM rho Henum Hlow M z <> C0.
Proof.
  intros r Hr M Hsm z Hz.
  assert (H0 : 0 <= KR r * Ttl rho Henum Hlow M).
  { pose proof (Ttl_nonneg rho Henum Hlow M). pose proof (KR_pos r Hr). nra. }
  pose proof (exp_half _ H0 Hsm) as Hhalf.
  assert (Hge : forall k, / 2 <= Cmod (Pprod (fun j => Efac z (rsh rho M j)) k))
    by (intro k; apply (tail_prod_ge rho Henum Hlow r Hr M Hhalf z ltac:(lra) k)).
  assert (Hlim : / 2 <= Cmod (TM rho Henum Hlow M z))
    by (apply (CUn_cv_mod_ge _ _ (/ 2) 0%nat (TM_spec rho Henum Hlow M z));
        intros n _; apply Hge).
  intro Hc. rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hlim. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the selector                                                   *)
(* ----------------------------------------------------------------- *)
Definition Msel (r : R) : nat :=
  natsel (fun n => KR r * Ttl rho Henum Hlow n) u0.

Lemma Msel_spec : forall r, 0 < r ->
  KR r * Ttl rho Henum Hlow (Msel r) < u0.
Proof.
  intros r Hr.
  pose proof (KR_pos r Hr) as HK. pose proof u0_pos as Hu.
  assert (Hex : exists n, KR r * Ttl rho Henum Hlow n < u0).
  { destruct (Ttl_small rho Henum Hlow (u0 / KR r)
                ltac:(apply Rdiv_lt_0_compat; lra)) as [n Hn].
    exists n.
    apply (Rmult_lt_reg_r (/ KR r)); [ apply Rinv_0_lt_compat; lra | ].
    replace (KR r * Ttl rho Henum Hlow n * / KR r) with (Ttl rho Henum Hlow n)
      by (field; lra).
    replace (u0 * / KR r) with (u0 / KR r) by (unfold Rdiv; ring). exact Hn. }
  unfold Msel.
  exact (natsel_spec (fun n => KR r * Ttl rho Henum Hlow n) u0 Hex).
Qed.

Theorem TM_Msel_ne0 : forall r, 0 < r ->
  forall z, Cmod z < r -> TM rho Henum Hlow (Msel r) z <> C0.
Proof.
  intros r Hr z Hz.
  apply (TM_ne0_disk r Hr (Msel r) (Msel_spec r Hr) z Hz).
Qed.

End Select.

Print Assumptions TM_Msel_ne0.

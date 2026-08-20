(* ================================================================= *)
(*  CZetaMod3.v  —  the projector applied to zeta's DIRICHLET SERIES.  *)
(*                                                                    *)
(*    zeta_split_finite : 3 . SUM_{k<N, k+1 = r mod 3} (k+1)^{-s}      *)
(*                        = SUM_{a<3} SUM_{k<N} om^{a(k+1+2r)}(k+1)^-s *)
(*    zeta_mod3_split   : the same for the CONVERGENT SERIES, Re s > 1 *)
(*                                                                    *)
(*  This is the contact point the cubic layer was built for.  The      *)
(*  a = 0 term is om^0 = 1 throughout, so it is zeta's own series      *)
(*  untouched; the a = 1 and a = 2 terms are its twists by the         *)
(*  additive characters of Z/3.  Read right to left, the identity says *)
(*  zeta plus its two twists reconstructs three times a single residue *)
(*  class -- the classical mod-3 decomposition, now available at any   *)
(*  residue r and for the actual convergent series rather than only    *)
(*  formally.                                                          *)
(*                                                                    *)
(*  INDEXING.  cterm s k is the term for n = k+1, so the residue class *)
(*  of interest is (k+1) mod 3, not k mod 3.  Rather than reindex the  *)
(*  series -- which would fight nat subtraction at k = 0 -- the split  *)
(*  is taken at residue r+2 and then transported by eq3_S, using       *)
(*  k = r+2 iff k+1 = r (mod 3).  The exponent moves the same way:     *)
(*  k + 2(r+2) and (k+1) + 2r differ by exactly 3, which om^3 = 1      *)
(*  absorbs.                                                          *)
(*                                                                    *)
(*  CONVERGENCE IS FREE.  |om^m| = 1, so every twisted series has the  *)
(*  SAME modulus bound as zeta's and reuses CZetaTerm.pseries_cv       *)
(*  unchanged -- the twist costs nothing analytically.  Axiom-clean.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus CSeries RootsOfUnity DFTInversion
        CZetaTerm CDirichlet COmega COmegaOrth.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the twist has modulus one                                      *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_C1' : Cmod C1 = 1.
Proof.
  replace C1 with (RtoC 1) by reflexivity.
  rewrite Cmod_RtoC. apply Rabs_R1.
Qed.

Lemma Cmod_om : Cmod om = 1.
Proof.
  unfold om, w, Cmod, Cnorm2. cbn [Re Im].
  replace (cos (2 * PI / INR 3) * cos (2 * PI / INR 3)
           + sin (2 * PI / INR 3) * sin (2 * PI / INR 3)) with 1
    by (pose proof (sin2_cos2 (2 * PI / INR 3)); unfold Rsqr in *; nra).
  apply sqrt_1.
Qed.

Lemma Cmod_om_pow : forall m, Cmod (Cpow om m) = 1.
Proof.
  induction m as [| m IH]; cbn [Cpow].
  - apply Cmod_C1'.
  - rewrite Cmod_mul, Cmod_om, IH. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the twisted and the residue-restricted terms                   *)
(* ----------------------------------------------------------------- *)
Definition ztw (s : C) (a r : nat) (k : nat) : C :=
  Cmul (Cpow om (a * (S k + 2 * r))%nat) (cterm s k).

Definition zres (s : C) (r : nat) (k : nat) : C :=
  Cmul (eq3 (S k) r) (cterm s k).

Lemma Cmod_ztw : forall s a r k, Cmod (ztw s a r k) = Cmod (cterm s k).
Proof. intros s a r k. unfold ztw. rewrite Cmod_mul, Cmod_om_pow. ring. Qed.

Lemma Cmod_zres : forall s r k, Cmod (zres s r k) <= Cmod (cterm s k).
Proof.
  intros s r k. unfold zres, eq3.
  destruct ((S k mod 3) =? (r mod 3))%nat.
  - rewrite Cmod_mul, Cmod_C1'. lra.
  - rewrite Cmod_mul, (proj2 (Cmod0 C0) eq_refl).
    pose proof (Cmod_nonneg (cterm s k)). lra.
Qed.

(* both converge on Re s > 1, against zeta's own majorant *)
Lemma ztw_cv : forall s a r, 1 < Re s -> { L | Cseries_cv (ztw s a r) L }.
Proof.
  intros s a r Hs.
  apply (Cseries_abs_cv (ztw s a r) (fun n => Rpower (INR (S n)) (- Re s))).
  - intro n. rewrite Cmod_ztw, Cmod_cterm. apply Rle_refl.
  - apply (pseries_cv (Re s)); exact Hs.
Qed.

Lemma zres_cv : forall s r, 1 < Re s -> { L | Cseries_cv (zres s r) L }.
Proof.
  intros s r Hs.
  apply (Cseries_abs_cv (zres s r) (fun n => Rpower (INR (S n)) (- Re s))).
  - intro n. rewrite <- Cmod_cterm. apply Cmod_zres.
  - apply (pseries_cv (Re s)); exact Hs.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  moving the split from k to n = k+1                             *)
(* ----------------------------------------------------------------- *)
Lemma eq3_S : forall k r, eq3 (S k) r = eq3 k (r + 2).
Proof.
  intros k r. unfold eq3.
  replace (S k) with (k + 1)%nat by lia.
  rewrite (Nat.Div0.add_mod k 1), (Nat.Div0.add_mod r 2).
  assert (Hk : (k mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hr : (r mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  destruct (k mod 3) as [|[|[|?]]]; destruct (r mod 3) as [|[|[|?]]];
    try lia; reflexivity.
Qed.

Lemma om_idx_S : forall a k r,
  Cpow om (a * (k + 2 * (r + 2)))%nat = Cpow om (a * (S k + 2 * r))%nat.
Proof.
  intros a k r.
  rewrite (om_pow_mod (a * (k + 2 * (r + 2)))%nat),
          (om_pow_mod (a * (S k + 2 * r))%nat).
  f_equal.
  assert (E : (a * (k + 2 * (r + 2)) = a * (S k + 2 * r) + 3 * a)%nat) by lia.
  rewrite E, Nat.Div0.add_mod.
  replace ((3 * a) mod 3)%nat with 0%nat
    by (symmetry; rewrite Nat.mul_comm; apply Nat.Div0.mod_mul).
  rewrite Nat.add_0_r. apply Nat.Div0.mod_mod.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the finite split                                               *)
(* ----------------------------------------------------------------- *)
Theorem zeta_split_finite : forall (s : C) (N r : nat),
  Cmul (RtoC (INR 3)) (Csum (zres s r) N)
  = Csum (fun a => Csum (ztw s a r) N) 3.
Proof.
  intros s N r.
  assert (HL : Csum (zres s r) N
               = Csum (fun k => Cmul (eq3 k (r + 2)) (cterm s k)) N).
  { apply Csum_ext. intro k. unfold zres. rewrite eq3_S. reflexivity. }
  assert (HR : Csum (fun a => Csum (ztw s a r) N) 3
               = Csum (fun a => Csum (fun k =>
                   Cmul (Cpow om (a * (k + 2 * (r + 2)))%nat) (cterm s k)) N) 3).
  { apply Csum_ext. intro a. apply Csum_ext. intro k. unfold ztw.
    rewrite om_idx_S. reflexivity. }
  rewrite HL, HR. apply residue_split.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  and for the convergent series                                  *)
(* ----------------------------------------------------------------- *)
Lemma Csum_3 : forall g : nat -> C,
  Csum g 3 = Cadd (g 0%nat) (Cadd (g 1%nat) (g 2%nat)).
Proof. intro g. cbn [Csum]. ring. Qed.

Lemma Cpsum_Csum : forall (a : nat -> C) (N : nat), Cpsum a N = Csum a (S N).
Proof.
  intros a N. induction N as [| N IH]; cbn [Cpsum Csum];
    [ ring | rewrite IH; reflexivity ].
Qed.

Lemma split_pointwise : forall (s : C) (N r : nat),
  Cmul (RtoC (INR 3)) (Cpsum (zres s r) N)
  = Cadd (Cpsum (ztw s 0 r) N)
         (Cadd (Cpsum (ztw s 1 r) N) (Cpsum (ztw s 2 r) N)).
Proof.
  intros s N r.
  pose proof (zeta_split_finite s (S N) r) as H.
  rewrite (Csum_3 (fun a => Csum (ztw s a r) (S N))) in H.
  rewrite !Cpsum_Csum. rewrite H. ring.
Qed.

Lemma CUn_cv_scal3 : forall (u : nat -> C) (l : C),
  CUn_cv u l -> CUn_cv (fun n => Cmul (RtoC (INR 3)) (u n)) (Cmul (RtoC (INR 3)) l).
Proof.
  intros u l Hu eps Heps.
  destruct (Hu (eps / 3) ltac:(lra)) as [N HN].
  exists N. intros n Hn.
  replace (Cminus (Cmul (RtoC (INR 3)) (u n)) (Cmul (RtoC (INR 3)) l))
    with (Cmul (RtoC (INR 3)) (Cminus (u n) l)) by ring.
  rewrite Cmod_mul, Cmod_RtoC.
  replace (INR 3) with 3 by (simpl; ring).
  rewrite Rabs_pos_eq by lra.
  pose proof (HN n Hn). lra.
Qed.

Theorem zeta_mod3_split : forall (s : C) (r : nat) (H : 1 < Re s),
  Cmul (RtoC (INR 3)) (proj1_sig (zres_cv s r H))
  = Cadd (proj1_sig (ztw_cv s 0 r H))
         (Cadd (proj1_sig (ztw_cv s 1 r H)) (proj1_sig (ztw_cv s 2 r H))).
Proof.
  intros s r H.
  destruct (zres_cv s r H) as [Lres HLres]. cbn [proj1_sig].
  destruct (ztw_cv s 0 r H) as [L0 HL0]. cbn [proj1_sig].
  destruct (ztw_cv s 1 r H) as [L1 HL1]. cbn [proj1_sig].
  destruct (ztw_cv s 2 r H) as [L2 HL2]. cbn [proj1_sig].
  apply (CUn_cv_unique (fun N => Cmul (RtoC (INR 3)) (Cpsum (zres s r) N))).
  - apply CUn_cv_scal3. exact HLres.
  - apply (CUn_cv_ext (fun N => Cadd (Cpsum (ztw s 0 r) N)
                        (Cadd (Cpsum (ztw s 1 r) N) (Cpsum (ztw s 2 r) N)))).
    + intro N. symmetry. apply split_pointwise.
    + apply CUn_cv_add; [ exact HL0 | apply CUn_cv_add; assumption ].
Qed.

Print Assumptions zeta_split_finite.
Print Assumptions zeta_mod3_split.

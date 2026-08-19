(* ================================================================= *)
(*  CCutoff.v  —  disk-cofactor bridge, cutoff foundation:              *)
(*  local extensionality of the complex derivative, and a Lipschitz     *)
(*  radial cutoff function.                                             *)
(*                                                                    *)
(*   is_Cderiv_ext_local : F = G on a ball around z => same derivative. *)
(*   psi r1 rc : a [0,1] cutoff, = 1 on [0,r1], = 0 on [rc,inf),        *)
(*     Lipschitz with constant 1/(rc-r1).                              *)
(*                                                                    *)
(*  These feed the construction of a globally-continuous g_cut that     *)
(*  agrees with g = F'/F on an inner disk (where g is holomorphic),     *)
(*  so the disk logarithm can be built by primitive_on_disk even though *)
(*  g itself has poles outside the disk.  Axiom-clean.                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic.
Open Scope R_scope.

(* ---- local extensionality of is_Cderiv ---- *)
Lemma is_Cderiv_ext_local : forall F G z d r, 0 < r ->
  (forall w, Cmod (Cminus w z) < r -> F w = G w) ->
  is_Cderiv G z d -> is_Cderiv F z d.
Proof.
  intros F G z d r Hr Heq HG eps Heps.
  destruct (HG eps Heps) as [del [Hdel Hb]].
  exists (Rmin del r); split; [ apply Rmin_pos; lra | ]. intros h Hh.
  assert (Hhdel : Cmod h < del) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (Hhr : Cmod h < r) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  assert (HFzh : F (Cadd z h) = G (Cadd z h))
    by (apply Heq; replace (Cminus (Cadd z h) z) with h by ring; exact Hhr).
  assert (HFz : F z = G z).
  { apply Heq; replace (Cminus z z) with C0 by ring;
      rewrite (proj2 (Cmod0 C0) eq_refl); exact Hr. }
  rewrite HFzh, HFz. apply Hb; exact Hhdel.
Qed.

(* ---- Rmax/Rmin are non-expansive ---- *)
Lemma Rmax_formula : forall c a, Rmax c a = (c + a + Rabs (a - c)) / 2.
Proof.
  intros c a; unfold Rmax; destruct (Rle_dec c a);
    [ rewrite (Rabs_pos_eq (a - c)) by lra | rewrite (Rabs_left (a - c)) by lra ]; lra.
Qed.

Lemma Rmin_formula : forall c a, Rmin c a = (c + a - Rabs (a - c)) / 2.
Proof.
  intros c a; unfold Rmin; destruct (Rle_dec c a);
    [ rewrite (Rabs_pos_eq (a - c)) by lra | rewrite (Rabs_left (a - c)) by lra ]; lra.
Qed.

Lemma Rmax_nonexp : forall c a b, Rabs (Rmax c a - Rmax c b) <= Rabs (a - b).
Proof.
  intros c a b. rewrite !Rmax_formula.
  pose proof (Rabs_triang_inv2 (a - c) (b - c)) as Hinv.
  replace (a - c - (b - c)) with (a - b) in Hinv by ring.
  replace ((c + a + Rabs (a - c)) / 2 - (c + b + Rabs (b - c)) / 2)
     with ((a - b) * / 2 + (Rabs (a - c) - Rabs (b - c)) * / 2) by lra.
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. lra.
Qed.

Lemma Rmin_nonexp : forall c a b, Rabs (Rmin c a - Rmin c b) <= Rabs (a - b).
Proof.
  intros c a b. rewrite !Rmin_formula.
  pose proof (Rabs_triang_inv2 (a - c) (b - c)) as Hinv.
  replace (a - c - (b - c)) with (a - b) in Hinv by ring.
  replace ((c + a - Rabs (a - c)) / 2 - (c + b - Rabs (b - c)) / 2)
     with ((a - b) * / 2 + - (Rabs (a - c) - Rabs (b - c)) * / 2) by lra.
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult, (Rabs_pos_eq (/ 2)) by lra.
  rewrite Rabs_Ropp. lra.
Qed.

(* ---- the radial cutoff ---- *)
Definition psi (r1 rc x : R) : R := Rmax 0 (Rmin 1 ((rc - x) / (rc - r1))).

Lemma psi_bounds : forall r1 rc x, 0 <= psi r1 rc x <= 1.
Proof.
  intros r1 rc x; unfold psi; split.
  - apply Rmax_l.
  - apply Rmax_lub; [ lra | apply Rmin_l ].
Qed.

Lemma psi_one : forall r1 rc x, r1 < rc -> x <= r1 -> psi r1 rc x = 1.
Proof.
  intros r1 rc x Hlt Hx; unfold psi.
  assert (H1 : 1 <= (rc - x) / (rc - r1)).
  { replace 1 with ((rc - r1) / (rc - r1)) by (field; lra).
    unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | lra ]. }
  rewrite (Rmin_left 1 _ H1). apply Rmax_right; lra.
Qed.

Lemma psi_zero : forall r1 rc x, r1 < rc -> rc <= x -> psi r1 rc x = 0.
Proof.
  intros r1 rc x Hlt Hx; unfold psi.
  assert (Hrr : 0 < rc - r1) by lra.
  assert (Hinv : 0 < / (rc - r1)) by (apply Rinv_0_lt_compat; exact Hrr).
  assert (H0 : (rc - x) / (rc - r1) <= 0).
  { unfold Rdiv; rewrite <- (Rmult_0_l (/ (rc - r1)));
      apply Rmult_le_compat_r; lra. }
  rewrite (Rmin_right 1 ((rc - x) / (rc - r1)) ltac:(lra)). apply Rmax_left; lra.
Qed.

Lemma psi_lip : forall r1 rc x y, r1 < rc ->
  Rabs (psi r1 rc x - psi r1 rc y) <= / (rc - r1) * Rabs (x - y).
Proof.
  intros r1 rc x y Hlt; unfold psi.
  eapply Rle_trans; [ apply Rmax_nonexp | ].
  eapply Rle_trans; [ apply Rmin_nonexp | ].
  replace ((rc - x) / (rc - r1) - (rc - y) / (rc - r1)) with ((y - x) / (rc - r1))
    by (field; lra).
  unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ (rc - r1))) by (left; apply Rinv_0_lt_compat; lra).
  rewrite (Rmult_comm (/ (rc - r1))).
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | ].
  rewrite <- Rabs_Ropp; replace (- (y - x)) with (x - y) by ring; apply Rle_refl.
Qed.

Print Assumptions psi_lip.

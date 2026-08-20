(* ================================================================= *)
(*  COmegaOrth.v  —  the Z/3 ORTHOGONALITY, and splitting a sum by    *)
(*  residue class mod 3.                                              *)
(*                                                                    *)
(*    om_pow_mod    : om^n depends only on n mod 3                    *)
(*    om_orth3      : SUM_{a<3} om^{a m} = 3 if 3 | m, else 0         *)
(*    residue_split : 3 . SUM_{n<N, n = r mod 3} f n                  *)
(*                    = SUM_{a<3} SUM_{n<N} om^{a(n + 2r)} . f n      *)
(*                                                                    *)
(*  This is what 1 + om + om^2 = 0 is FOR.  As an identity it is       *)
(*  inert; as an orthogonality relation it is a projector, and         *)
(*  residue_split is that projector applied to an arbitrary sum:       *)
(*  the terms with n = r (mod 3) are picked out and the rest cancel.   *)
(*  Applied to a Dirichlet series it splits SUM a_n n^{-s} by residue  *)
(*  class -- which is the contact point with the zeta side, since      *)
(*  zeta's own series is what gets split.                             *)
(*                                                                    *)
(*  WHY om^{a(n + 2r)} AND NOT om^{a(n-r)}.  Subtraction on nat        *)
(*  truncates, so n - r is wrong as soon as n < r.  Since om^3 = 1,    *)
(*  om^{-1} = om^2, so om^{-ar} = om^{2ar} and n + 2r is the correct   *)
(*  index -- exact, total, and no integers needed.  The bookkeeping    *)
(*  then reduces to (n + 2r) = 0 (mod 3) iff n = r (mod 3), which is   *)
(*  nine concrete cases.                                              *)
(*                                                                    *)
(*  Everything rests on RootsOfUnity.dft_orthogonality_delta, which    *)
(*  has been general in N all along; only N = 3 had never been taken.  *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus RootsOfUnity DFTInversion COmega.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  om^n sees only n mod 3                                         *)
(* ----------------------------------------------------------------- *)
Lemma om_pow_mod : forall n, Cpow om n = Cpow om (n mod 3).
Proof.
  intro n.
  assert (E : (n = 3 * (n / 3) + n mod 3)%nat) by apply Nat.Div0.div_mod.
  assert (H : Cpow om ((3 * (n / 3) + n mod 3)%nat) = Cpow om (n mod 3)).
  { rewrite Cpow_add, Cpow_mul, om_pow3, Cpow_C1. ring. }
  rewrite <- H. f_equal. exact E.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the orthogonality relation at N = 3                            *)
(* ----------------------------------------------------------------- *)
Lemma om_orth3 : forall m,
  Csum (fun a => Cpow om (a * m)%nat) 3
  = (if Nat.eqb (m mod 3) 0 then RtoC (INR 3) else C0).
Proof.
  intro m.
  assert (Hlt : (m mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  pose proof (dft_orthogonality_delta 3 (m mod 3) Hlt) as H.
  fold om in H.
  rewrite <- H.
  apply Csum_ext. intro a.
  rewrite <- Cpow_mul.
  rewrite (om_pow_mod (a * m)%nat), (om_pow_mod (m mod 3 * a)%nat).
  f_equal.
  rewrite (Nat.Div0.mul_mod (m mod 3) a), (Nat.Div0.mul_mod a m).
  rewrite Nat.Div0.mod_mod.
  f_equal. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the residue-class indicator                                    *)
(* ----------------------------------------------------------------- *)
Definition eq3 (n r : nat) : C :=
  if Nat.eqb (n mod 3) (r mod 3) then C1 else C0.

Lemma mod3_shift : forall n r,
  ((n + 2 * r) mod 3 =? 0)%nat = ((n mod 3) =? (r mod 3))%nat.
Proof.
  intros n r.
  rewrite Nat.Div0.add_mod, (Nat.Div0.mul_mod 2 r).
  assert (Hn : (n mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hr : (r mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  destruct (n mod 3) as [|[|[|?]]]; destruct (r mod 3) as [|[|[|?]]];
    try lia; reflexivity.
Qed.

Lemma om_orth3_shift : forall n r,
  Csum (fun a => Cpow om (a * (n + 2 * r))%nat) 3 = Cmul (RtoC (INR 3)) (eq3 n r).
Proof.
  intros n r. rewrite om_orth3, mod3_shift. unfold eq3.
  destruct ((n mod 3) =? (r mod 3))%nat; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE PROJECTOR                                                  *)
(* ----------------------------------------------------------------- *)
Theorem residue_split : forall (f : nat -> C) (N r : nat),
  Cmul (RtoC (INR 3)) (Csum (fun n => Cmul (eq3 n r) (f n)) N)
  = Csum (fun a => Csum (fun n => Cmul (Cpow om (a * (n + 2 * r))%nat) (f n)) N) 3.
Proof.
  intros f N r.
  rewrite (Csum_swap (fun a n => Cmul (Cpow om (a * (n + 2 * r))%nat) (f n)) 3 N).
  rewrite Csum_scale_l.
  apply Csum_ext. intro n.
  rewrite <- Csum_scale_r, om_orth3_shift. ring.
Qed.

Print Assumptions om_orth3.
Print Assumptions residue_split.

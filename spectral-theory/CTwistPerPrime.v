(* ================================================================= *)
(*  CTwistPerPrime.v  --  the 3-4-1 per-prime inequality, twisted.     *)
(*                                                                    *)
(*  Toward L(1+it, chi) <> 0.  EulerFactorLog.per_prime_log is stated  *)
(*  in terms of an ANGLE phi:                                          *)
(*                                                                    *)
(*      0 <= 3 L 0 r + 4 L phi r + L (2 phi) r,   L th r =             *)
(*                          - (1/2) ln (1 - 2 r cos th + r^2)          *)
(*                                                                    *)
(*  For zeta the angle is handed to you: the Euler factor at p is      *)
(*  1 - p^{-(a+ib)}, whose argument is -b ln p.  For a character twist *)
(*  the factor is 1 - chi(q) q^{-(a+ib)} and the argument involves     *)
(*  arg chi(q) -- but this repo deliberately has no Carg, and we do    *)
(*  not want one.                                                      *)
(*                                                                    *)
(*  THE WAY AROUND: reparametrise by c = cos phi instead of phi.       *)
(*  cos (2 phi) = 2 c^2 - 1, so the inequality becomes a statement     *)
(*  about (r, c) with -1 <= c <= 1, and acos supplies the angle only   *)
(*  inside the proof.  Downstream, c is produced algebraically as      *)
(*  Re z1 / r -- no argument function is ever needed.                  *)
(*                                                                    *)
(*  Also here: the dual group law at the dchar level (chi_a chi_b =    *)
(*  chi_{a+b}), which the repo proves only for the abstract characters *)
(*  of Z/NZ and never transports.  It is what makes chi^2 = chi_{2a}.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory.
Require Import ComplexField Cmodulus RootsOfUnity ZmodOrder DirichletModP
        LogGeomSeries EulerFactorLog.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  1.  the dual group law for dchar                                   *)
(* ----------------------------------------------------------------- *)

Lemma dchar_index_add : forall p g a b n,
  Cmul (dchar p g a n) (dchar p g b n) = dchar p g (a + b) n.
Proof.
  intros p g a b n. unfold dchar.
  destruct (n mod p =? 0)%nat.
  - ring.
  - rewrite <- Cpow_add. f_equal. ring.
Qed.

Corollary dchar_sq : forall p g a n,
  Cmul (dchar p g a n) (dchar p g a n) = dchar p g (2 * a) n.
Proof.
  intros p g a n. rewrite dchar_index_add. f_equal. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  the 3-4-1 inequality, reparametrised by c = cos phi            *)
(* ----------------------------------------------------------------- *)

Definition Lc (c r : R) : R := - (/ 2) * ln (1 - 2 * r * c + r ^ 2).

Lemma L_is_Lc : forall th r, L th r = Lc (cos th) r.
Proof. intros th r. unfold L, Lc. reflexivity. Qed.

Theorem per_prime_log_c : forall c r, 0 <= r < 1 -> -1 <= c <= 1 ->
  0 <= 3 * Lc 1 r + 4 * Lc c r + Lc (2 * c * c - 1) r.
Proof.
  intros c r Hr Hc.
  pose proof (per_prime_log (acos c) r Hr) as H.
  rewrite !L_is_Lc in H.
  rewrite cos_0 in H.
  rewrite (cos_acos c Hc) in H.
  (* cos (2 * acos c) = 2 c^2 - 1 *)
  assert (Hd : cos (2 * acos c) = 2 * c * c - 1).
  { rewrite cos_2a.
    pose proof (sin2_cos2 (acos c)) as Hpy. unfold Rsqr in Hpy.
    rewrite (cos_acos c Hc) in Hpy |- *. nra. }
  rewrite Hd in H. exact H.
Qed.

Print Assumptions dchar_index_add.
Print Assumptions per_prime_log_c.

(* ================================================================= *)
(*  END CTwistPerPrime.v                                              *)
(* ================================================================= *)

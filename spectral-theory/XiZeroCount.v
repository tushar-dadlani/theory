(* ================================================================= *)
(*  XiZeroCount.v  —  THE HADAMARD KEYSTONE TARGET, for xi.            *)
(*                                                                    *)
(*    xi_zero_count : for every circle radius Rc > 0 there are a       *)
(*      finite list l of zeros of XiC and a Jensen radius              *)
(*      Rc/8 <= Rj < Rc/4                                              *)
(*      such that                                                     *)
(*                                                                    *)
(*        every rho in l is a genuine zero, 0 < |rho| < Rj            *)
(*        l is COMPLETE: every zero of XiC in |z| < Rj lies in l      *)
(*        INR (length l) <= ln (4 . (1/2 + (Rc+1)^2 . Tgb (Rc+1)))     *)
(*                            / ln 3                                   *)
(*        (#{rho in l : |rho| <= Rj/2}) . ln 2                         *)
(*            <= (1/2PI) INT ln|xi(Rj e^{it})| dt - ln|xi(0)|.        *)
(*                                                                    *)
(*  The third clause is n(r) = O(r ln r): Tgb(s) = exp(O(s ln s))      *)
(*  (XiGrowthBound), so its logarithm is O(Rc ln Rc).  That is the     *)
(*  Hadamard-keystone counting bound, and it arrives WITHOUT Jensen's  *)
(*  formula -- it is the elementary Cauchy decay estimate of           *)
(*  CPeelBound.  The fourth clause is the Jensen count itself, which   *)
(*  now also has every hypothesis discharged.                          *)
(*                                                                    *)
(*  The three inputs xi has to supply are exactly:                     *)
(*    holomorphy   RiemannXiEntire.XiC_entire  (entire, so every disk) *)
(*    nonvanishing XiNonzero.XiC_ne0_at0       (xi(0) = 1/2 <> 0)      *)
(*    growth       XiGrowthBound.XiC_growth    (order 1)               *)
(*  Continuity is not a separate input: holo_ptcont derives it from    *)
(*  holomorphy.  Axiom-clean.                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus CHoloCcontC
        CPathIntegral CSegInt JensenMultiZero JensenCount CZeroListFactor
        JensenCountComplete RiemannXiEntire XiNonzero XiGrowthBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  holomorphic ==> pointwise continuous.  is_Cderiv_cont states this  *)
(*  in increment form (F (z + h) vs F z); ptcont wants it in           *)
(*  two-point form.  Same step as inside CHoloCcontC.holo_CcontC.      *)
(* ----------------------------------------------------------------- *)
(* holo_ptcont now lives in CHoloCcontC, next to holo_CcontC *)

(* ----------------------------------------------------------------- *)
(*  xi's three inputs, in the shape the counting theorem consumes      *)
(* ----------------------------------------------------------------- *)
Lemma XiC_holo : forall z, exists d, is_Cderiv XiC z d.
Proof. intro z. exact (XiC_entire z I). Qed.

Lemma XiC_disk_holo : forall R, disk_holo XiC R.
Proof. intros R z _. apply XiC_holo. Qed.

Lemma XiC_ptcont : ptcont XiC.
Proof. exact (holo_ptcont XiC XiC_holo). Qed.

(* the circle bound, from the order-1 growth *)
Definition XiM (Rc : R) : R := / 2 + (Rc + 1) ^ 2 * Tgb (Rc + 1).

Lemma XiC_circle_bound : forall Rc, 0 < Rc ->
  forall u, Cmod (XiC (arc Rc u)) <= XiM Rc.
Proof.
  intros Rc HRc u. unfold XiM.
  rewrite <- (Cmod_arc Rc u ltac:(lra)) at 2 3.
  apply XiC_growth.
Qed.

Lemma Cmod_XiC_C0 : Cmod (XiC C0) = / 2.
Proof.
  rewrite XiC_C0. unfold Cmod, Cnorm2, RtoC; cbn [Re Im].
  replace (/ 2 * / 2 + 0 * 0) with (Rsqr (/ 2)) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE COUNT                                                          *)
(* ----------------------------------------------------------------- *)
Theorem xi_zero_count : forall Rc : R, 0 < Rc ->
  exists (l : list C) (Rj : R),
    0 < Rj /\ Rj < Rc / 4 /\ Rc / 8 <= Rj /\
    (forall rho, In rho l -> 0 < Cmod rho < Rj) /\
    (forall rho, In rho l -> XiC rho = C0) /\
    (forall z, Cmod z < Rj -> XiC z = C0 -> In z l) /\
    INR (length l) <= ln (4 * XiM Rc) / ln 3 /\
    forall pr : Riemann_integrable (fun t => ln (Cmod (XiC (arc Rj t)))) 0 (2 * PI),
      INR (count_le (Rj / 2) l) * ln 2
      <= RiemannInt pr / (2 * PI) - ln (Cmod (XiC C0)).
Proof.
  intros Rc HRc.
  destruct (jensen_count_complete XiC (Rc + 2) Rc (XiM Rc) HRc ltac:(lra)
              XiC_ne0_at0 XiC_ptcont (XiC_disk_holo (Rc + 2))
              (XiC_circle_bound Rc HRc))
    as [l [Rj [HRj0 [HRjb [HRjlo [Hin [Hzero [Hcomp [Hcount Hjensen]]]]]]]]].
  exists l, Rj.
  split; [ exact HRj0 | ]. split; [ exact HRjb | ]. split; [ exact HRjlo | ].
  split; [ exact Hin | ]. split; [ exact Hzero | ].
  split; [ exact Hcomp | ]. split; [ | exact Hjensen ].
  (* 2 * XiM Rc / Cmod (XiC C0) = 4 * XiM Rc, since |xi(0)| = 1/2 *)
  rewrite Cmod_XiC_C0 in Hcount.
  replace (4 * XiM Rc) with (2 * XiM Rc / / 2) by (field; lra).
  exact Hcount.
Qed.

Print Assumptions xi_zero_count.

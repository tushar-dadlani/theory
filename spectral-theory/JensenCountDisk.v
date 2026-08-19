(* ================================================================= *)
(*  JensenCountDisk.v  —  the JENSEN COUNTING INEQUALITY on a DISK.     *)
(*                                                                    *)
(*    jensen_count_D :  for F = (prod_{rho in l}(z - rho)) . G with G   *)
(*    holomorphic and zero-free on the disk Cmod z < R2 only, and       *)
(*    0 < Rr < R2, all zeros 0 < |rho| < Rr:                            *)
(*                                                                    *)
(*      (#{rho in l : |rho| <= Rr/2}) . ln 2                            *)
(*          <= (1/2PI) INT_0^{2PI} ln|F(Rr e^{it})| dt  -  ln|F(0)|.    *)
(*                                                                    *)
(*  Same statement as JensenCount.jensen_count, but with the cofactor   *)
(*  hypotheses relaxed from ENTIRE zero-free to DISK zero-free (and     *)
(*  with HcontG dropped) -- the form the xi cofactor G_R = xi/P_R       *)
(*  actually satisfies.  The counting half is untouched: count_le,      *)
(*  prodfac_C0_ne0 and count_bound are facts about the zero LIST and    *)
(*  the value at C0 alone, so they are imported from JensenCount, not   *)
(*  re-derived.  Only the Jensen identity changes hands, from           *)
(*  jensen_multi_zero to jensen_multi_zero_D.  Axiom-clean.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List.
Require Import ComplexField Cmodulus Holomorphic CPathIntegral CSegInt
        CDeriv JensenMultiZero JensenCount JensenMultiZeroDisk.
Open Scope R_scope.

Theorem jensen_count_D : forall (G Gp : C -> C) (R2 Rr : R) (l : list C)
  (HR : 0 < Rr) (HRR2 : Rr < R2)
  (HGhol : forall z, Cmod z < R2 -> is_Cderiv G z (Gp z))
  (HGphol : forall z, Cmod z < R2 -> exists d, is_Cderiv Gp z d)
  (HGne0 : forall z, Cmod z < R2 -> G z <> C0)
  (Hin : forall rho, In rho l -> 0 < Cmod rho < Rr)
  (pr : Riemann_integrable
          (fun t => ln (Cmod (Cmul (prodfac l (arc Rr t)) (G (arc Rr t))))) 0 (2 * PI)),
  INR (count_le (Rr / 2) l) * ln 2
  <= RiemannInt pr / (2 * PI) - ln (Cmod (Cmul (prodfac l C0) (G C0))).
Proof.
  intros.
  assert (HC0in : Cmod C0 < R2) by (rewrite (proj2 (Cmod0 C0) eq_refl); lra).
  assert (Hin' : forall rho, In rho l -> Cmod rho < Rr) by (intros rho Hr; apply (Hin rho Hr)).
  rewrite (jensen_multi_zero_D G Gp R2 Rr HR HRR2 HGhol HGphol HGne0 l Hin' pr).
  assert (Hpi : 0 < 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (Hprodne : prodfac l C0 <> C0)
    by (apply prodfac_C0_ne0; intros r Hr; apply (proj1 (Hin r Hr))).
  rewrite Cmod_mul,
    (ln_mult (Cmod (prodfac l C0)) (Cmod (G C0))
       (cmod_pos _ Hprodne) (cmod_pos _ (HGne0 C0 HC0in))).
  replace (2 * PI * (INR (length l) * ln Rr + ln (Cmod (G C0))) / (2 * PI))
     with (INR (length l) * ln Rr + ln (Cmod (G C0))) by (field; lra).
  pose proof (count_bound Rr l HR Hin) as Hcb. lra.
Qed.

Print Assumptions jensen_count_D.

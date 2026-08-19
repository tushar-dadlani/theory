(* ================================================================= *)
(*  JensenCountZeros.v  —  the Jensen count, stated about F and its     *)
(*  ZEROS rather than about a pre-factored product.                     *)
(*                                                                    *)
(*    jensen_count_zeros :  F = prodfac l . G on a disk, G zero-free    *)
(*      and regular there, zeros 0 < |rho| < Rr  ==>                    *)
(*                                                                    *)
(*        (#{rho in l : |rho| <= Rr/2}) . ln 2                          *)
(*           <= (1/2PI) INT_0^{2PI} ln|F(Rr e^{it})| dt  -  ln|F(0)|.   *)
(*                                                                    *)
(*  This is the join that shows brick 1 actually lands.  The cofactor   *)
(*  G here is precisely what CZeroListFactor.DivBy_distinct hands back  *)
(*  from a list of distinct zeros of F, and the two hypotheses          *)
(*  jensen_count_D wanted as a NAMED derivative pair (HGhol, HGphol)    *)
(*  are manufactured on the spot by CDerivHoloDisk.holo_deriv_fun_radius*)
(*  -- no choice axiom, since the tower names the derivative itself.    *)
(*                                                                    *)
(*  What is still hypothesis, and is the whole remaining programme:     *)
(*  HGne0, that the cofactor has NO zeros left on the disk.  That is    *)
(*  true exactly when l is the COMPLETE zero multiset there, which      *)
(*  needs (a) finite order of vanishing at each zero and (b) finiteness *)
(*  of the zero set -- the identity theorem at an arbitrary centre, and *)
(*  a 2D Bolzano-Weierstrass.  Axiom-clean.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CPathIntegral CSegInt
        CDeriv JensenMultiZero JensenCount JensenCountDisk CDerivHoloDisk
        CZeroListFactor.
Open Scope R_scope.

Theorem jensen_count_zeros : forall (F G : C -> C) (R2 Rr : R) (l : list C),
  0 < Rr -> Rr < R2 ->
  (forall z, F z = Cmul (prodfac l z) (G z)) ->
  ptcont G ->
  (forall z, Cmod z < 2 * R2 + 1 -> exists d, is_Cderiv G z d) ->
  (forall z, Cmod z < R2 -> G z <> C0) ->
  (forall rho, In rho l -> 0 < Cmod rho < Rr) ->
  forall (pr : Riemann_integrable (fun t => ln (Cmod (F (arc Rr t)))) 0 (2 * PI)),
  INR (count_le (Rr / 2) l) * ln 2
  <= RiemannInt pr / (2 * PI) - ln (Cmod (F C0)).
Proof.
  intros F G R2 Rr l HR HRR2 Hid HGptc HGhol HGne0 Hin.
  assert (HR2 : 0 < R2) by lra.
  (* the named derivative pair jensen_count_D asks for, from the tower *)
  destruct (holo_deriv_fun_radius G R2 HR2 HGptc HGhol) as [Gp [HGp HGpp]].
  (* F and the product have the SAME integrand, pointwise *)
  assert (Hfun : (fun t => ln (Cmod (F (arc Rr t))))
               = (fun t => ln (Cmod (Cmul (prodfac l (arc Rr t)) (G (arc Rr t))))))
    by (apply functional_extensionality; intro t; rewrite (Hid (arc Rr t)); reflexivity).
  assert (HF0 : Cmod (F C0) = Cmod (Cmul (prodfac l C0) (G C0)))
    by (rewrite (Hid C0); reflexivity).
  rewrite Hfun, HF0. intro pr.
  exact (jensen_count_D G Gp R2 Rr l HR HRR2 HGp HGpp HGne0 Hin pr).
Qed.

Print Assumptions jensen_count_zeros.

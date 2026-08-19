(* ================================================================= *)
(*  CCentreBound.v  —  the value at the centre is bounded by the       *)
(*  maximum on the circle.                                             *)
(*                                                                    *)
(*    centre_bound : G pointwise-continuous and holomorphic on          *)
(*      Cmod z < Rr + 1, with Cmod (G (arc Rr u)) <= M for all u        *)
(*        ==>  Cmod (G C0) <= 2 * M.                                    *)
(*                                                                    *)
(*  Cauchy's formula at the centre (cauchy_interior_dom at w = C0)      *)
(*  says  oint G(z)/z dz = 2 pi i . G(0);  the integrand there has      *)
(*  modulus  |G| . (1/Rr) . Rr = |G| <= M,  so pathint_ML bounds the    *)
(*  loop by 4 pi M and dividing by 2 pi gives the claim.                *)
(*                                                                    *)
(*  The constant 2 is Cintf_ML's Re/Im split, not the true maximum      *)
(*  principle (which would give 1).  It is harmless everywhere it is    *)
(*  used: the peel estimate it feeds (CPeelBound) multiplies it against *)
(*  a geometric factor (1/3)^n, so any fixed constant is absorbed.      *)
(*                                                                    *)
(*  Note the hypotheses are the LIGHT ones -- pointwise continuity plus *)
(*  holomorphy stated existentially.  In particular no derivative       *)
(*  FUNCTION and none of the CMeanValueDisk package (CcontC of the      *)
(*  derivative, arc_Fp_unif) is needed, which is what makes this usable *)
(*  directly on a peel cofactor.  Axiom-clean.                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral PerronRemovable RootsOfUnity CCauchyAnalytic CRemovableExtDom.
Open Scope R_scope.

Lemma Cpow_one : forall x : C, Cpow x 1 = x.
Proof. intro x; cbn; ring. Qed.

Lemma Cmod_2PIi : Cmod (mkC 0 (2 * PI)) = 2 * PI.
Proof.
  pose proof PI_RGT_0 as HPI.
  unfold Cmod, Cnorm2; cbn [Re Im].
  replace (0 * 0 + 2 * PI * (2 * PI)) with (Rsqr (2 * PI)) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr; [ reflexivity | lra ].
Qed.

Theorem centre_bound : forall (G : C -> C) (Rr M : R),
  0 < Rr ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (G z') (G z)) < eps) ->
  (forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv G z d) ->
  (forall u, Cmod (G (arc Rr u)) <= M) ->
  Cmod (G C0) <= 2 * M.
Proof.
  intros G Rr M HR Hptc Hhol Hbd.
  pose proof PI_RGT_0 as HPI.
  assert (HmodC0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 C0)); reflexivity).
  assert (HC0R : Cmod C0 < Rr) by lra.
  assert (HGc : CcontC G) by (apply ptcont_CcontC; exact Hptc).
  destruct (Hhol C0 ltac:(lra)) as [d0 Hd0].
  (* the circle never meets the centre *)
  assert (Harc_ne0 : forall u, arc Rr u <> C0).
  { intros u Hc.
    assert (Hm : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
    rewrite Hc, HmodC0 in Hm. lra. }
  assert (Harcne : forall u, Cminus (arc Rr u) C0 <> C0).
  { intro u. replace (Cminus (arc Rr u) C0) with (arc Rr u) by ring. apply Harc_ne0. }
  (* continuity of the Cauchy kernel, as in CAnalyticTowerF.fseq0_eq *)
  assert (Hpc : Ccont (fun u => Cmul (Cmul (G (arc Rr u))
                                  (Cinv (Cminus (arc Rr u) C0))) (arc' Rr u))).
  { assert (Hfe : (fun u => Cmul (Cmul (G (arc Rr u))
                             (Cinv (Cminus (arc Rr u) C0))) (arc' Rr u))
                  = Kwn G Rr 1 C0)
      by (apply functional_extensionality; intro u; unfold Kwn;
          rewrite Cpow_one; reflexivity).
    rewrite Hfe. exact (Kwn_cont G Rr 1 HGc C0 Harcne). }
  (* Cauchy at the centre *)
  pose proof (cauchy_interior_dom G Rr C0 d0 HR HC0R Hd0 Hptc
                (fun z Hz (_ : z <> C0) => Hhol z Hz) Hpc) as Hcauchy.
  (* the kernel is bounded by M on the circle: |G| . (1/Rr) . Rr *)
  assert (Hml : forall u, 0 <= u <= 2 * PI ->
      Cmod (Cmul ((fun z => Cmul (G z) (Cinv (Cminus z C0))) (arc Rr u)) (arc' Rr u)) <= M).
  { intros u _. cbv beta.
    replace (Cminus (arc Rr u) C0) with (arc Rr u) by ring.
    rewrite !Cmod_mul, (Cmod_inv (arc Rr u) (Harc_ne0 u)),
            (Cmod_arc Rr u ltac:(lra)), (Cmod_arc' Rr u ltac:(lra)).
    replace (Cmod (G (arc Rr u)) * / Rr * Rr) with (Cmod (G (arc Rr u)))
      by (field; lra).
    apply Hbd. }
  pose proof (pathint_ML (arc Rr) (arc' Rr)
                (fun z => Cmul (G z) (Cinv (Cminus z C0))) Hpc 0 (2 * PI) M
                ltac:(lra) Hml) as HML.
  rewrite Hcauchy, Cmod_mul, Cmod_2PIi in HML.
  apply (Rmult_le_reg_l (2 * PI)); [ lra | ].
  replace (2 * PI * (2 * M)) with (2 * M * (2 * PI - 0)) by ring.
  exact HML.
Qed.

Print Assumptions centre_bound.

(* ================================================================= *)
(*  CEisensteinSupp2.v  --  the second supplementary law, reduced.     *)
(*                                                                    *)
(*  THE LAW ITSELF IS NOT PROVED HERE, AND IS NOT PROVED ANYWHERE IN   *)
(*  THIS DEVELOPMENT.  What is proved is that its two classical forms  *)
(*  are the SAME theorem:                                             *)
(*                                                                    *)
(*    supp2_iff :  chi_pi(1-om) = om^{2(a+1)/3}                        *)
(*            <->  chi_pi(3)    = om^{2b/3}                            *)
(*                                                                    *)
(*  for a primary pi = a + b om of prime norm p >= 7.  So the missing  *)
(*  input is exactly one named classical theorem -- Gauss's cubic      *)
(*  character of 3 -- and not two independent gaps.                   *)
(*                                                                    *)
(*  WHY IT CANNOT BE REACHED FROM THE RECIPROCITY TOWER.  3 ramifies:  *)
(*  3 = -om^2 (1-om)^2, so multiplicativity gives ONE equation,        *)
(*                                                                    *)
(*      chi(3) = chi(om)^2 chi(1-om)^2,          (chiv_three)          *)
(*                                                                    *)
(*  in the two unknowns, and there is no second one.  Reciprocity is   *)
(*  silent at 3: N(1-om) = 3, and (3-1)/3 is not an integer, so the    *)
(*  residue field F_3 carries no cubic character at all.  Every chiv   *)
(*  lemma in the tower carries pi | t - om, which is the SPLITTING     *)
(*  hypothesis.  chi(1-om^2) gives nothing new either, since           *)
(*  1 - om^2 = conj(1-om) = -om^2 (1-om) is an associate.             *)
(*                                                                    *)
(*  The whole content of the reduction is one arithmetic identity,     *)
(*  primary_exp_id: for a = 3u-1 and b = 3v the norm satisfies         *)
(*                                                                    *)
(*      u  =  2v + (N-1)/3   (mod 3),                                  *)
(*                                                                    *)
(*  i.e. the two exponents differ by exactly the exponent of the FIRST *)
(*  supplementary law, chiv_omega.  That is why they stand or fall     *)
(*  together.  Checked against brute force on all 17822 primary (a,b)  *)
(*  in [-200,200]^2 with 3 not dividing the norm: no violations; and   *)
(*  both forms of the law hold with no violations on all 74 primary    *)
(*  primes of norm below 900.                                         *)
(*  Axiom-free.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia.
Require Import CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinResidue
        CEisensteinGcd CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinPrimary CEisensteinCubicFun CEisensteinNormJ
        CEisensteinRamified.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  mu_3 written additively                                        *)
(* ----------------------------------------------------------------- *)
Definition ompow (k : Z) : Eis :=
  if (k mod 3 =? 0) then eone
  else if (k mod 3 =? 1) then eom
  else emul eom eom.

Lemma ompow_mod : forall k, ompow (k mod 3) = ompow k.
Proof. intro k. unfold ompow. rewrite Zmod_mod. reflexivity. Qed.

Lemma ompow_cong : forall j k, (j - k) mod 3 = 0 -> ompow j = ompow k.
Proof.
  intros j k H.
  assert (E : j mod 3 = k mod 3).
  { apply (proj1 (Z.mod_divide (j - k) 3 ltac:(lia))) in H.
    destruct H as [c Hc].
    replace j with (k + c * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  unfold ompow. rewrite E. reflexivity.
Qed.

Lemma ompow_add : forall j k, ompow (j + k) = emul (ompow j) (ompow k).
Proof.
  intros j k.
  rewrite <- (ompow_mod (j + k)), Zplus_mod.
  assert (Hj : 0 <= j mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (Hk : 0 <= k mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  unfold ompow.
  set (x := j mod 3) in *. set (y := k mod 3) in *.
  assert (Hx : x = 0 \/ x = 1 \/ x = 2) by lia.
  assert (Hy : y = 0 \/ y = 1 \/ y = 2) by lia.
  destruct Hx as [-> | [-> | ->]]; destruct Hy as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma ompow_cuberoot : forall k, cuberoot (ompow k).
Proof.
  intro k. unfold ompow, cuberoot.
  destruct (k mod 3 =? 0); [ left; reflexivity | ].
  destruct (k mod 3 =? 1); [ right; left; reflexivity | right; right; reflexivity ].
Qed.

(* the bridge to the nat-exponent form used by chiv_omega *)
Lemma ompow_nat : forall n : nat, ompow (Z.of_nat n) = epow eom (n mod 3)%nat.
Proof.
  intro n.
  assert (Hm : Z.of_nat n mod 3 = Z.of_nat (n mod 3)%nat).
  { rewrite (Nat2Z.inj_mod n 3). reflexivity. }
  assert (Hc : (n mod 3 = 0 \/ n mod 3 = 1 \/ n mod 3 = 2)%nat)
    by (pose proof (Nat.mod_upper_bound n 3 ltac:(lia)); lia).
  unfold ompow. rewrite Hm.
  destruct Hc as [E | [E | E]]; rewrite E; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  two facts about cube roots of unity                            *)
(* ----------------------------------------------------------------- *)
Lemma cuberoot_cube_eq : forall z, cuberoot z -> emul z (emul z z) = eone.
Proof. intros z [-> | [-> | ->]]; reflexivity. Qed.

Lemma cuberoot_pow4 : forall z, cuberoot z -> emul (emul z z) (emul z z) = z.
Proof. intros z [-> | [-> | ->]]; reflexivity. Qed.

Lemma econj_invol : forall z, econj (econj z) = z.
Proof. intros [a b]; unfold econj; cbn [ea eb]; apply Eis_eq; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  C.  THE ARITHMETIC IDENTITY                                        *)
(* ----------------------------------------------------------------- *)
(*  a = 3u - 1, b = 3v, N = a^2 - ab + b^2, N - 1 = 3w                *)
(*      ==>  u - (2v + w)  is divisible by 3.                          *)
Lemma primary_exp_id : forall u v w : Z,
  (3 * u - 1) * (3 * u - 1) - (3 * u - 1) * (3 * v) + (3 * v) * (3 * v) - 1
    = 3 * w ->
  u - (2 * v + w) = 3 * (u - v - u * u + u * v - v * v).
Proof.
  intros u v w H.
  assert (Hw : w = 3 * (u * u) - 2 * u - 3 * (u * v) + v + 3 * (v * v)) by nia.
  rewrite Hw. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the law, both ways round                                       *)
(* ----------------------------------------------------------------- *)
Section Supp2.

Variable p : nat.
Variable pi : Eis.
Variable t : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdiv : Nat.divide 3 (p - 1)%nat.
Hypothesis Hn : enorm pi = Z.of_nat p.
Hypothesis Ht : edvd pi (esub (eZ t) eom).
Hypothesis Hpr : primary pi.

Lemma pi_irred2 : eirred pi.
Proof. exact (norm_prime_eirred pi (Z.of_nat p) Hp Hn). Qed.

Lemma pi_ndvd_lam : ~ edvd pi elam.
Proof. apply (pi_ndvd_elam pi (Z.of_nat p) Hn). lia. Qed.

(* -----  chi(-1) = 1, at the chiv level  ----- *)
Lemma pi_ndvd_mone : ~ edvd pi (eopp eone).
Proof.
  intros [q Hq].
  assert (H1 : edvd pi eone).
  { exists (eopp q).
    assert (E2 : emul pi (eopp q) = eopp (emul pi q)) by ring.
    rewrite E2, <- Hq. reflexivity. }
  destruct pi_irred2 as [Hnu _].
  exact (Hnu (proj1 (edvd_eone pi) H1)).
Qed.

Theorem chiv_minus_one : chiv p pi (eopp eone) = eone.
Proof.
  pose proof (chiv_cube p pi t Hp Hp7 Hdiv Hn Ht (eopp eone) pi_ndvd_mone) as H.
  replace (epow (eopp eone) 3) with (eopp eone) in H by reflexivity.
  exact H.
Qed.

(* -----  the ONE equation: chi(3) = chi(om)^2 chi(1-om)^2  ----- *)
Theorem chiv_three :
  chiv p pi (eZ 3)
  = emul (emul (chiv p pi eom) (chiv p pi eom))
         (emul (chiv p pi elam) (chiv p pi elam)).
Proof.
  pose proof (chiv_mul p pi t Hp Hp7 Hdiv Hn Ht) as CM.
  assert (E : eZ 3 = emul (eopp eone) (emul (emul eom eom) (emul elam elam)))
    by reflexivity.
  rewrite E, !CM, chiv_minus_one. ring.
Qed.

Theorem chiv_lam_sq :
  emul (chiv p pi elam) (chiv p pi elam)
  = emul (chiv p pi (eZ 3)) (chiv p pi eom).
Proof.
  assert (HW : cuberoot (chiv p pi eom))
    by (apply (chiv_cuberoot p pi Hp Hn);
        exact (pi_ndvd_omega pi pi_irred2)).
  rewrite chiv_three.
  set (W := chiv p pi eom) in *. set (L := chiv p pi elam).
  assert (Eg : emul (emul (emul W W) (emul L L)) W
             = emul (emul W (emul W W)) (emul L L)) by ring.
  rewrite Eg, (cuberoot_cube_eq W HW), emul_1. reflexivity.
Qed.

Theorem chiv_lam_solve :
  chiv p pi elam = econj (emul (chiv p pi (eZ 3)) (chiv p pi eom)).
Proof.
  assert (HL : cuberoot (chiv p pi elam))
    by (apply (chiv_cuberoot p pi Hp Hn); exact pi_ndvd_lam).
  rewrite <- chiv_lam_sq, (cuberoot_sq _ HL), econj_invol. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  THE EQUIVALENCE                                                *)
(* ----------------------------------------------------------------- *)
Definition UU : Z := (ea pi + 1) / 3.
Definition VV : Z := eb pi / 3.
Definition WW : Z := Z.of_nat ((p - 1) / 3).

Lemma ea_form : ea pi = 3 * UU - 1.
Proof.
  destruct Hpr as [Ha _]. unfold UU.
  pose proof (Z.div_mod (ea pi + 1) 3 ltac:(lia)) as H.
  assert (Hm : (ea pi + 1) mod 3 = 0).
  { rewrite (Zplus_mod (ea pi) 1), Ha. reflexivity. }
  lia.
Qed.

Lemma eb_form : eb pi = 3 * VV.
Proof.
  destruct Hpr as [_ Hb]. unfold VV.
  pose proof (Z.div_mod (eb pi) 3 ltac:(lia)) as H. lia.
Qed.

Lemma norm_form : Z.of_nat p - 1 = 3 * WW.
Proof.
  unfold WW.
  destruct Hdiv as [c Hc].
  assert (Hd : ((p - 1) / 3 = c)%nat) by (rewrite Hc, Nat.div_mul; lia).
  rewrite Hd.
  assert (Hz : Z.of_nat (p - 1)%nat = Z.of_nat c * 3)
    by (rewrite Hc, Nat2Z.inj_mul; reflexivity).
  rewrite Nat2Z.inj_sub in Hz by lia. cbn in Hz. lia.
Qed.

Lemma exp_id : UU - (2 * VV + WW) = 3 * (UU - VV - UU * UU + UU * VV - VV * VV).
Proof.
  apply primary_exp_id.
  pose proof norm_form as HN.
  assert (HE : enorm pi = ea pi * ea pi - ea pi * eb pi + eb pi * eb pi)
    by reflexivity.
  rewrite ea_form, eb_form in HE. rewrite Hn in HE. lia.
Qed.

Lemma chiv_om_ompow : chiv p pi eom = ompow WW.
Proof.
  rewrite (chiv_omega p pi t Hp Hp7 Hdiv Hn Ht). unfold WW.
  rewrite ompow_nat. reflexivity.
Qed.

(*  The two classical forms of the second supplementary law.           *)
Definition SL2_lam   : Prop := chiv p pi elam    = ompow (2 * UU).
Definition SL2_three : Prop := chiv p pi (eZ 3)  = ompow (2 * VV).

Theorem supp2_iff : SL2_lam <-> SL2_three.
Proof.
  pose proof exp_id as EI.
  pose proof chiv_om_ompow as HW.
  assert (HL : cuberoot (chiv p pi elam))
    by (apply (chiv_cuberoot p pi Hp Hn); exact pi_ndvd_lam).
  unfold SL2_lam, SL2_three. split.
  - (* chi(1-om) known  ==>  chi(3) known *)
    intro H1.
    assert (Hsq : emul (chiv p pi (eZ 3)) (chiv p pi eom) = ompow (4 * UU)).
    { rewrite <- chiv_lam_sq, H1, <- ompow_add. f_equal. ring. }
    (* multiply through by chi(om)^2, which is chi(om)^{-1} *)
    assert (Hmul : emul (emul (chiv p pi (eZ 3)) (chiv p pi eom))
                        (emul (chiv p pi eom) (chiv p pi eom))
                 = emul (chiv p pi (eZ 3))
                        (emul (chiv p pi eom)
                              (emul (chiv p pi eom) (chiv p pi eom)))) by ring.
    assert (HW3 : emul (chiv p pi eom) (emul (chiv p pi eom) (chiv p pi eom)) = eone)
      by (rewrite HW; apply cuberoot_cube_eq; apply ompow_cuberoot).
    assert (Hstep : chiv p pi (eZ 3)
                  = emul (ompow (4 * UU)) (emul (ompow WW) (ompow WW))).
    { rewrite <- Hsq, <- HW, Hmul, HW3. ring. }
    rewrite Hstep, <- !ompow_add.
    apply ompow_cong. rewrite (proj2 (Z.mod_divide _ 3 ltac:(lia)));
      [ reflexivity | exists (4 * (UU - VV - UU * UU + UU * VV - VV * VV)
                              + 2 * VV + 2 * WW); lia ].
  - (* chi(3) known  ==>  chi(1-om) known *)
    intro H2.
    assert (Hsq : emul (chiv p pi elam) (chiv p pi elam) = ompow (2 * VV + WW))
      by (rewrite chiv_lam_sq, H2, HW, <- ompow_add; reflexivity).
    assert (H4 : chiv p pi elam = ompow (2 * (2 * VV + WW))).
    { rewrite <- (cuberoot_pow4 _ HL), Hsq, <- ompow_add. f_equal. ring. }
    rewrite H4. apply ompow_cong.
    rewrite (proj2 (Z.mod_divide _ 3 ltac:(lia)));
      [ reflexivity | exists (- 2 * (UU - VV - UU * UU + UU * VV - VV * VV)); lia ].
Qed.

End Supp2.

Print Assumptions ompow_add.
Print Assumptions primary_exp_id.
Print Assumptions chiv_minus_one.
Print Assumptions chiv_three.
Print Assumptions chiv_lam_sq.
Print Assumptions chiv_lam_solve.
Print Assumptions supp2_iff.

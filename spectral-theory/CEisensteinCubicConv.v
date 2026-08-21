(* ================================================================= *)
(*  CEisensteinCubicConv.v  —  the CONVERSE of Euler's criterion.      *)
(*                                                                    *)
(*    cube_root_of_unity_is_cube : in (Z/p)^*, r^{(p-1)/3} = 1         *)
(*      implies r is a cube                                           *)
(*    cubic_residue_converse     : chi_pi(alpha) = 1 implies alpha is  *)
(*      a cube mod pi                                                  *)
(*    euler_criterion_cubic      : the two directions, as an iff       *)
(*                                                                    *)
(*  UNTIL NOW THE SYMBOL WAS ONLY A CHARACTER.  cubic_symbol says      *)
(*  alpha^{(p-1)/3} is congruent to exactly one cube root of unity,    *)
(*  cubic_symbol_mul says the assignment is multiplicative, and        *)
(*  cubic_symbol_cube says cubes land on 1.  None of that tells you    *)
(*  the symbol DETECTS cubic residues -- for all those results know,   *)
(*  the value 1 might be taken by non-cubes as well.  This file        *)
(*  closes that gap, and it is what makes chi_pi worth computing.      *)
(*                                                                    *)
(*  THE ARGUMENT NEVER TOUCHES Z[om].  The residue field is Z/p, and   *)
(*  the statement is a fact about the cyclic group (Z/p)^*: an element *)
(*  killed by (p-1)/3 is a cube.  Write r = g^i for a primitive root   *)
(*  g; then g^{i(p-1)/3} = 1 forces (p-1) | i(p-1)/3, hence 3 | i,     *)
(*  hence r = (g^{i/3})^3.  PrimitiveRoot.units_cyclic supplies g and  *)
(*  root_is_power supplies i, so the group theory is already done --   *)
(*  what is left is transport, in both directions, across             *)
(*  CEisensteinResidue.int_cong_iff.                                   *)
(*                                                                    *)
(*  THE TRANSPORT IS THE ACTUAL WORK, and it is the same shape as in   *)
(*  efermat: replace alpha by the integer r = (ea + eb t) mod p that   *)
(*  represents it, using cong_int and the fact that pi divides         *)
(*  t - om; run the Z/p argument on r; carry the cube s back as        *)
(*  eZ s.  r is nonzero precisely because pi does not divide alpha,    *)
(*  which is where the hypothesis is spent.                            *)
(*                                                                    *)
(*  ONE HYPOTHESIS IS INHERITED AND WORTH NAMING: the witness t with   *)
(*  pi | t - om.  It comes from CEisensteinSplit.eisenstein_split_     *)
(*  witness and is what pins the residue field to Z/p rather than to   *)
(*  an abstract quotient; every result in this layer carries it.       *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicSupp.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the group-theoretic core, entirely inside Z/p                  *)
(* ----------------------------------------------------------------- *)
Theorem cube_root_of_unity_is_cube : forall p r,
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  (1 <= r <= p - 1)%nat -> pw p r ((p - 1) / 3) = 1%nat ->
  exists s, (1 <= s <= p - 1)%nat /\ pw p s 3 = r.
Proof.
  intros p r Hp Hp7 Hdiv Hr Hroot.
  destruct Hdiv as [q Hq].
  assert (Hq3 : ((p - 1) / 3 = q)%nat) by (rewrite Hq; apply Nat.div_mul; lia).
  rewrite Hq3 in Hroot.
  assert (Hq1 : (1 <= q)%nat) by lia.
  (* Fermat for r, obtained by cubing the hypothesis *)
  assert (Hfer : pw p r (p - 1)%nat = 1%nat).
  { rewrite Hq, pw_mul_exp, Hroot. apply pw_1; lia. }
  destruct (units_cyclic p Hp) as [g [Hg Hgord]].
  destruct (root_is_power p g (p - 1)%nat r Hp Hg Hgord Hr Hfer) as [i [Hi Hgi]].
  assert (H3i : Nat.divide 3 i).
  { assert (Hgq : pw p g (i * q)%nat = 1%nat)
      by (rewrite pw_mul_exp, Hgi; exact Hroot).
    pose proof (ord_divides p g (i * q)%nat Hp Hg Hgq) as Hd.
    rewrite Hgord, Hq in Hd.
    destruct Hd as [c Hc]. exists c. nia. }
  destruct H3i as [c Hc].
  exists (pw p g c). split.
  - apply pw_unit; assumption.
  - rewrite <- pw_mul_exp, <- Hc. exact Hgi.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  transport to Z[om]                                             *)
(* ----------------------------------------------------------------- *)
Theorem cubic_residue_converse : forall (p : nat) (pi : Eis) (t : Z) (alpha : Eis),
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  enorm pi = Z.of_nat p ->
  edvd pi (esub (eZ t) eom) ->
  ~ edvd pi alpha ->
  econg pi (epow alpha ((p - 1) / 3)) eone ->
  exists beta, ~ edvd pi beta /\ econg pi alpha (epow beta 3).
Proof.
  intros p pi t alpha Hp Hp7 Hdiv Hn Ht Hna Hsym.
  set (P := Z.of_nat p).
  assert (HP : 7 <= P) by (unfold P; lia).
  pose proof (pi_dvd_p pi P Hn) as Hpip.
  (* alpha is congruent to an integer, and then to its residue *)
  pose proof (cong_int pi t alpha Ht) as Hm.
  set (m := ea alpha + eb alpha * t).
  set (rZ := m mod P).
  assert (HrZ : 0 <= rZ < P) by (unfold rZ; apply Z.mod_pos_bound; lia).
  assert (Hmr : (P | m - rZ)) by (exists (m / P); unfold rZ; rewrite Z.mod_eq; lia).
  assert (Hcongmr : econg pi (eZ m) (eZ rZ)).
  { unfold econg. rewrite <- eZ_sub.
    apply (proj2 (int_cong_iff pi P (m - rZ) Hp Hn Hpip)). exact Hmr. }
  assert (Halr : econg pi alpha (eZ rZ))
    by (apply (econg_trans pi alpha (eZ m) (eZ rZ)); assumption).
  assert (Hr0 : rZ <> 0).
  { intro Hc. apply Hna.
    assert (Hz : econg pi alpha (eZ 0)) by (rewrite <- Hc; exact Halr).
    destruct Hz as [w Hw]. exists w.
    unfold esub, eZ, eadd, eopp in Hw; cbn [ea eb] in Hw.
    rewrite <- Hw. destruct alpha as [aa ab]; apply Eis_eq; cbn [ea eb]; ring. }
  (* the small nat representative *)
  set (r := Z.to_nat rZ).
  assert (Hr : Z.of_nat r = rZ) by (unfold r; apply Z2Nat.id; lia).
  assert (Hrange : (1 <= r <= p - 1)%nat) by (unfold P in *; lia).
  (* the symbol hypothesis, moved onto r *)
  assert (Hsymr : econg pi (epow (eZ rZ) ((p - 1) / 3)) eone).
  { apply (econg_trans pi _ (epow alpha ((p - 1) / 3)) _); [ | exact Hsym ].
    apply econg_sym. apply econg_pow. exact Halr. }
  rewrite epow_eZ in Hsymr.
  assert (Hdvd : (P | rZ ^ Z.of_nat ((p - 1) / 3) - 1)).
  { apply (proj1 (int_cong_iff pi P _ Hp Hn Hpip)).
    unfold econg in Hsymr. rewrite <- eZ_one, <- eZ_sub in Hsymr. exact Hsymr. }
  (* ... and turned into a nat statement *)
  assert (Hpw : pw p r ((p - 1) / 3) = 1%nat).
  { apply Nat2Z.inj. unfold pw.
    rewrite Nat2Z.inj_mod, Nat2Z.inj_pow, Hr.
    replace (Z.of_nat p) with P by reflexivity.
    replace (Z.of_nat 1) with 1 by reflexivity.
    destruct Hdvd as [c Hc].
    replace (rZ ^ Z.of_nat ((p - 1) / 3)) with (1 + c * P) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_1_l; lia. }
  (* the group-theoretic core *)
  destruct (cube_root_of_unity_is_cube p r Hp Hp7 Hdiv Hrange Hpw) as [s [Hs Hs3]].
  assert (HsZ : 0 < Z.of_nat s < P) by (unfold P in *; lia).
  exists (eZ (Z.of_nat s)). split.
  - (* pi does not divide the witness *)
    intro Hd.
    apply (proj1 (int_cong_iff pi P (Z.of_nat s) Hp Hn Hpip)) in Hd.
    destruct Hd as [c Hc].
    destruct (Z.le_gt_cases c 0) as [Hc0 | Hc0].
    + assert (c * P <= 0 * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    + assert (1 * P <= c * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - (* and it cubes back to alpha *)
    rewrite epow_eZ.
    apply (econg_trans pi alpha (eZ rZ) _); [ exact Halr | ].
    unfold econg. rewrite <- eZ_sub.
    apply (proj2 (int_cong_iff pi P _ Hp Hn Hpip)).
    assert (E : (Z.of_nat s ^ Z.of_nat 3) mod P = rZ).
    { rewrite <- Hr, <- Hs3. unfold pw.
      rewrite Nat2Z.inj_mod, Nat2Z.inj_pow. reflexivity. }
    assert (Hd1 : (P | Z.of_nat s ^ Z.of_nat 3 - rZ)).
    { apply Z.mod_divide; [ lia | ].
      rewrite Zminus_mod, E, (Z.mod_small rZ P HrZ), Z.sub_diag.
      apply Zmod_0_l. }
    destruct Hd1 as [c Hc]. exists (- c). lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Euler's criterion for cubes, both ways                         *)
(* ----------------------------------------------------------------- *)
Theorem euler_criterion_cubic : forall (p : nat) (pi : Eis) (t : Z) (alpha : Eis),
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  enorm pi = Z.of_nat p ->
  edvd pi (esub (eZ t) eom) ->
  ~ edvd pi alpha ->
  (econg pi (epow alpha ((p - 1) / 3)) eone
   <-> exists beta, ~ edvd pi beta /\ econg pi alpha (epow beta 3)).
Proof.
  intros p pi t alpha Hp Hp7 Hdiv Hn Ht Hna. split.
  - intro H. exact (cubic_residue_converse p pi t alpha Hp Hp7 Hdiv Hn Ht Hna H).
  - intros [beta [Hnb Hcong]].
    apply (econg_trans pi _ (epow (epow beta 3) ((p - 1) / 3)) _).
    + apply econg_pow. exact Hcong.
    + exact (cubic_symbol_cube p pi t beta Hp Hp7 Hdiv Hn Ht Hnb).
Qed.

Print Assumptions cube_root_of_unity_is_cube.
Print Assumptions cubic_residue_converse.
Print Assumptions euler_criterion_cubic.

(* ================================================================= *)
(*  CEisensteinPrimary.v  —  primary normalization in Z[omega].        *)
(*                                                                    *)
(*    primary z        :=  ea z = 2 mod 3  /\  eb z = 0 mod 3          *)
(*    primary_exists   :  3 does not divide N(z)  =>                   *)
(*                          some associate of z is primary             *)
(*    primary_unique   :  at most one associate of z is primary        *)
(*    primary_prime    :  the two, packaged for a prime norm           *)
(*                                                                    *)
(*  WHY THIS IS NEEDED AT ALL.  The cubic residue symbol chi_pi is     *)
(*  NOT invariant under replacing pi by an associate: pi and om.pi     *)
(*  have the same norm p, but (p-1)/3 is unchanged while the           *)
(*  congruence class of alpha^{(p-1)/3} is taken modulo a different    *)
(*  generator.  Reciprocity therefore cannot even be STATED until a    *)
(*  canonical representative is pinned down among the six associates,  *)
(*  and "primary" -- pi congruent to -1 modulo 3 -- is that choice.    *)
(*                                                                    *)
(*  THE WHOLE THING IS A FINITE VERIFICATION, and pleasantly so.       *)
(*  N(a + b om) = a^2 - ab + b^2 is divisible by 3 exactly when        *)
(*  (a,b) mod 3 lands in {(0,0), (1,2), (2,1)}, so the SIX surviving   *)
(*  residue classes are matched against the SIX units, and the         *)
(*  matching is a bijection:                                          *)
(*                                                                    *)
(*      (2,0) -> 1      (1,0) -> -1      (1,1) -> om                   *)
(*      (2,2) -> -om    (0,2) -> om^2    (0,1) -> -om^2                *)
(*                                                                    *)
(*  That six-against-six coincidence is not luck.  Multiplication by   *)
(*  a unit acts on (a,b) mod 3 by an invertible linear map, the six    *)
(*  units act simply transitively on the six classes, and "primary"    *)
(*  names one orbit point.  Existence and uniqueness are the two       *)
(*  halves of that transitivity, which is why they cost about the      *)
(*  same here.                                                        *)
(*                                                                    *)
(*  Uniqueness is proved in the sharper form primary_unit_one: if w    *)
(*  and w.u are both primary then u = 1.  Cancelling by the inverse    *)
(*  of a unit -- which is its conjugate, since N(u) = 1 -- reduces     *)
(*  the general statement to that one, so only six cases are ever      *)
(*  examined rather than thirty-six.                                  *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia.
Require Import CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinUnique
        CEisensteinUFD.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  residues mod 3                                                 *)
(* ----------------------------------------------------------------- *)
Lemma mod3_cases : forall a : Z, a mod 3 = 0 \/ a mod 3 = 1 \/ a mod 3 = 2.
Proof. intro a. pose proof (Z.mod_pos_bound a 3 ltac:(lia)). lia. Qed.

Lemma mod3_of : forall k r : Z, 0 <= r < 3 -> (3 * k + r) mod 3 = r.
Proof.
  intros k r Hr.
  rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia.
  apply Z.mod_small; lia.
Qed.

Lemma mod3_split : forall a : Z, exists k, a = 3 * k + a mod 3.
Proof. intro a. exists (a / 3). pose proof (Z.div_mod a 3 ltac:(lia)). lia. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the norm mod 3 sees only the residues                          *)
(* ----------------------------------------------------------------- *)
Lemma enorm_mod3_form : forall a b : Z, exists k : Z,
  a * a - a * b + b * b
  = 3 * k + ((a mod 3) * (a mod 3) - (a mod 3) * (b mod 3) + (b mod 3) * (b mod 3)).
Proof.
  intros a b.
  destruct (mod3_split a) as [qa Ha].
  destruct (mod3_split b) as [qb Hb].
  set (ra := a mod 3) in *. set (rb := b mod 3) in *.
  exists (3*qa*qa + 2*qa*ra + 3*qb*qb + 2*qb*rb - 3*qa*qb - qa*rb - ra*qb).
  rewrite Ha at 1 2 3. rewrite Hb at 1 2 3. ring.
Qed.

(* the three classes killed by 3, and the six that survive *)
Theorem three_ndvd_norm_cases : forall z : Eis, ~ (3 | enorm z) ->
  (ea z mod 3 = 0 /\ eb z mod 3 = 1) \/ (ea z mod 3 = 0 /\ eb z mod 3 = 2)
  \/ (ea z mod 3 = 1 /\ eb z mod 3 = 0) \/ (ea z mod 3 = 1 /\ eb z mod 3 = 1)
  \/ (ea z mod 3 = 2 /\ eb z mod 3 = 0) \/ (ea z mod 3 = 2 /\ eb z mod 3 = 2).
Proof.
  intros [a b] Hnd; cbn [ea eb] in *.
  unfold enorm in Hnd; cbn [ea eb] in Hnd.
  destruct (enorm_mod3_form a b) as [k Hk].
  destruct (mod3_cases a) as [Ha | [Ha | Ha]];
  destruct (mod3_cases b) as [Hb | [Hb | Hb]];
    rewrite Ha, Hb in Hk;
    try (exfalso; apply Hnd;
         first [ exists k; lia | exists (k + 1); lia ]);
    tauto.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  primary                                                        *)
(* ----------------------------------------------------------------- *)
Definition primary (z : Eis) : Prop := ea z mod 3 = 2 /\ eb z mod 3 = 0.

(* the six units, as coordinate maps *)
Lemma emul_u_1 : forall a b, emul (mkEis a b) eone = mkEis a b.
Proof. intros a b. rewrite emul_comm. apply emul_1. Qed.

Lemma emul_u_m1 : forall a b, emul (mkEis a b) (mkEis (-1) 0) = mkEis (-a) (-b).
Proof. intros a b. unfold emul; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma emul_u_om : forall a b, emul (mkEis a b) (mkEis 0 1) = mkEis (-b) (a - b).
Proof. intros a b. unfold emul; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma emul_u_mom : forall a b, emul (mkEis a b) (mkEis 0 (-1)) = mkEis b (b - a).
Proof. intros a b. unfold emul; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma emul_u_om2 : forall a b, emul (mkEis a b) (mkEis (-1) (-1)) = mkEis (b - a) (-a).
Proof. intros a b. unfold emul; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma emul_u_mom2 : forall a b, emul (mkEis a b) (mkEis 1 1) = mkEis (a - b) a.
Proof. intros a b. unfold emul; cbn [ea eb]. apply Eis_eq; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  D.  EXISTENCE                                                      *)
(* ----------------------------------------------------------------- *)
Theorem primary_exists : forall z : Eis, ~ (3 | enorm z) ->
  exists u, eunit u /\ primary (emul z u).
Proof.
  intros z Hnd.
  pose proof (three_ndvd_norm_cases z Hnd) as Hc.
  destruct z as [a b]; cbn [ea eb] in Hc.
  destruct (mod3_split a) as [ka Ha]. destruct (mod3_split b) as [kb Hb].
  destruct Hc as [[H1 H2] | [[H1 H2] | [[H1 H2] | [[H1 H2] | [[H1 H2] | [H1 H2]]]]]];
    rewrite H1 in Ha; rewrite H2 in Hb.
  - (* (0,1) -> -om^2 = mkEis 1 1 *)
    exists (mkEis 1 1). split; [ apply norm_eunit; reflexivity | ].
    rewrite emul_u_mom2. unfold primary; cbn [ea eb]. split.
    + replace (a - b) with (3 * (ka - kb - 1) + 2) by lia. apply mod3_of; lia.
    + replace a with (3 * ka + 0) by lia. apply mod3_of; lia.
  - (* (0,2) -> om^2 = mkEis (-1) (-1) *)
    exists (mkEis (-1) (-1)). split; [ apply norm_eunit; reflexivity | ].
    rewrite emul_u_om2. unfold primary; cbn [ea eb]. split.
    + replace (b - a) with (3 * (kb - ka) + 2) by lia. apply mod3_of; lia.
    + replace (-a) with (3 * (- ka) + 0) by lia. apply mod3_of; lia.
  - (* (1,0) -> -1 *)
    exists (mkEis (-1) 0). split; [ apply norm_eunit; reflexivity | ].
    rewrite emul_u_m1. unfold primary; cbn [ea eb]. split.
    + replace (-a) with (3 * (- ka - 1) + 2) by lia. apply mod3_of; lia.
    + replace (-b) with (3 * (- kb) + 0) by lia. apply mod3_of; lia.
  - (* (1,1) -> om *)
    exists (mkEis 0 1). split; [ apply norm_eunit; reflexivity | ].
    rewrite emul_u_om. unfold primary; cbn [ea eb]. split.
    + replace (-b) with (3 * (- kb - 1) + 2) by lia. apply mod3_of; lia.
    + replace (a - b) with (3 * (ka - kb) + 0) by lia. apply mod3_of; lia.
  - (* (2,0) -> 1 *)
    exists eone. split; [ apply eunit_one | ].
    rewrite emul_u_1. unfold primary; cbn [ea eb]. split.
    + replace a with (3 * ka + 2) by lia. apply mod3_of; lia.
    + replace b with (3 * kb + 0) by lia. apply mod3_of; lia.
  - (* (2,2) -> -om = mkEis 0 (-1) *)
    exists (mkEis 0 (-1)). split; [ apply norm_eunit; reflexivity | ].
    rewrite emul_u_mom. unfold primary; cbn [ea eb]. split.
    + replace b with (3 * kb + 2) by lia. apply mod3_of; lia.
    + replace (b - a) with (3 * (kb - ka) + 0) by lia. apply mod3_of; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  UNIQUENESS                                                     *)
(* ----------------------------------------------------------------- *)
Lemma primary_unit_one : forall w u,
  eunit u -> primary w -> primary (emul w u) -> u = eone.
Proof.
  intros w u Hu Hw Hwu.
  destruct w as [a b]. destruct Hw as [Ha Hb]; cbn [ea eb] in Ha, Hb.
  destruct (eunits_six u Hu) as [E | [E | [E | [E | [E | E]]]]]; subst u.
  - reflexivity.
  - exfalso. rewrite emul_u_m1 in Hwu. destruct Hwu as [H _]; cbn [ea eb] in H.
    destruct (mod3_split a) as [k Hk]; rewrite Ha in Hk.
    replace (- a) with (3 * (- k - 1) + 1) in H by lia.
    rewrite mod3_of in H by lia. lia.
  - exfalso. rewrite emul_u_om in Hwu. destruct Hwu as [H _]; cbn [ea eb] in H.
    destruct (mod3_split b) as [k Hk]; rewrite Hb in Hk.
    replace (- b) with (3 * (- k) + 0) in H by lia.
    rewrite mod3_of in H by lia. lia.
  - exfalso. rewrite emul_u_mom in Hwu. destruct Hwu as [H _]; cbn [ea eb] in H.
    destruct (mod3_split b) as [k Hk]; rewrite Hb in Hk.
    replace (b) with (3 * k + 0) in H by lia.
    rewrite mod3_of in H by lia. lia.
  - exfalso. rewrite emul_u_mom2 in Hwu. destruct Hwu as [_ H]; cbn [ea eb] in H.
    destruct (mod3_split a) as [k Hk]; rewrite Ha in Hk.
    replace (a) with (3 * k + 2) in H by lia.
    rewrite mod3_of in H by lia. lia.
  - exfalso. rewrite emul_u_om2 in Hwu. destruct Hwu as [_ H]; cbn [ea eb] in H.
    destruct (mod3_split a) as [k Hk]; rewrite Ha in Hk.
    replace (- a) with (3 * (- k - 1) + 1) in H by lia.
    rewrite mod3_of in H by lia. lia.
Qed.

Lemma eunit_econj : forall u, eunit u -> eunit (econj u).
Proof. intros u Hu. apply norm_eunit. rewrite enorm_econj. exact (eunit_norm u Hu). Qed.

Lemma eunit_econj_inv : forall u, eunit u -> emul u (econj u) = eone.
Proof.
  intros u Hu. rewrite emul_econj, (eunit_norm u Hu). reflexivity.
Qed.

Theorem primary_unique : forall z u v, eunit u -> eunit v ->
  primary (emul z u) -> primary (emul z v) -> emul z u = emul z v.
Proof.
  intros z u v Hu Hv Hzu Hzv.
  set (t := emul (econj u) v).
  assert (Ht : eunit t) by (apply eunit_mul; [ apply eunit_econj | ]; assumption).
  assert (Hstep : emul (emul z u) t = emul z v).
  { unfold t.
    transitivity (emul z (emul (emul u (econj u)) v)); [ ring | ].
    rewrite (eunit_econj_inv u Hu). ring. }
  assert (Hone : t = eone).
  { apply (primary_unit_one (emul z u) t Ht Hzu). rewrite Hstep. exact Hzv. }
  rewrite <- Hstep, Hone. ring.
Qed.

(* the same, at the level of the unit *)
Corollary primary_unit_unique : forall z u v, eunit u -> eunit v ->
  z <> ezero -> primary (emul z u) -> primary (emul z v) -> u = v.
Proof.
  intros z u v Hu Hv Hz Hzu Hzv.
  apply (emul_cancel z _ _ Hz).
  exact (primary_unique z u v Hu Hv Hzu Hzv).
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  packaged for a prime norm                                      *)
(* ----------------------------------------------------------------- *)
Theorem primary_prime : forall (pi : Eis) (p : Z),
  prime p -> p <> 3 -> enorm pi = p ->
  exists u, eunit u /\ primary (emul pi u) /\ enorm (emul pi u) = p.
Proof.
  intros pi p Hp H3 Hn.
  assert (Hnd : ~ (3 | enorm pi)).
  { rewrite Hn. intro Hd.
    destruct (prime_divisors p Hp 3 Hd) as [E | [E | [E | E]]]; try lia.
    destruct Hp as [Hp1 _]; lia. }
  destruct (primary_exists pi Hnd) as [u [Hu Hpr]].
  exists u. split; [ exact Hu | split; [ exact Hpr | ] ].
  rewrite enorm_mul, (eunit_norm u Hu), Hn. ring.
Qed.

Print Assumptions primary_exists.
Print Assumptions primary_unique.
Print Assumptions primary_unit_unique.
Print Assumptions primary_prime.

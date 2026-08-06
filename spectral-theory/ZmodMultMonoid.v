(* ================================================================= *)
(*  ZmodMultMonoid.v  —  Brick 3 core:  (Z/p, x) ~= Adj((Z/p)^x).      *)
(*                                                                    *)
(*  PRIMALITY IS ZERO-ADJUNCTION.  For prime p every nonzero residue    *)
(*  is a unit, so the multiplicative monoid (Z/p, x) is exactly the      *)
(*  unit group with an absorbing zero adjoined:                         *)
(*      phi : Rp -> Adj Up,   0 |-> AZero,   nonzero x |-> AElt x        *)
(*  is a bijection carrying residue-multiplication to aop.              *)
(*                                                                    *)
(*  Carriers are sig types over BOOLEAN predicates:                     *)
(*      Rp = { x : nat | x <? p = true }            (residues)          *)
(*      Up = { x : nat | (0 <? x) && (x <? p) = true } (units)          *)
(*  Injectivity of the pair uses boolean UIP (Eqdep_dec.UIP_dec on       *)
(*  bool_dec) -- axiom-free, no proof_irrelevance.  The unit closure     *)
(*  and nonvanishing of a product of units come from ZmodPStar          *)
(*  (mulmod_in_units), which is where PRIMALITY enters.  Axiom-free.     *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia ZArith Znumtheory FinFun Eqdep_dec Bool.
Require Import ZmodPStar MonoidAlgebraZero HopfGroupAlgebraGen.
Open Scope nat_scope.

(* ---- boolean UIP: sig over a bool predicate is a set ---- *)
Lemma sig_eq_bool :
  forall (P : nat -> bool) (a b : nat) (pa : P a = true) (pb : P b = true),
    a = b -> exist (fun x => P x = true) a pa = exist (fun x => P x = true) b pb.
Proof.
  intros P a b pa pb Hab; subst b.
  rewrite (UIP_dec bool_dec pa pb); reflexivity.
Qed.

Section ZmodPrime.

Variable p : nat.
Hypothesis Hp : prime (Z.of_nat p).

Lemma p_ge2 : 2 <= p.
Proof. pose proof (prime_ge_2 _ Hp) as H; lia. Qed.

(* ---- the two sig carriers ---- *)
Definition is_unit_b (x : nat) : bool := (0 <? x) && (x <? p).
Definition Up : Type := { x : nat | is_unit_b x = true }.
Definition Rp : Type := { x : nat | (x <? p) = true }.

Lemma Up_eq : forall u v : Up, proj1_sig u = proj1_sig v -> u = v.
Proof. intros [a Ha] [b Hb] H; cbn in H; apply sig_eq_bool; exact H. Qed.

Lemma Rp_eq : forall u v : Rp, proj1_sig u = proj1_sig v -> u = v.
Proof. intros [a Ha] [b Hb] H; cbn in H; apply sig_eq_bool; exact H. Qed.

Lemma AElt_cong : forall u v : Up, proj1_sig u = proj1_sig v -> AElt Up u = AElt Up v.
Proof. intros u v H; rewrite (Up_eq u v H); reflexivity. Qed.

(* ---- unit bookkeeping ---- *)
Lemma unit_bounds : forall a, is_unit_b a = true -> 1 <= a <= p - 1.
Proof.
  intros a H; unfold is_unit_b in H; apply andb_true_iff in H.
  destruct H as [H1 H2]; apply Nat.ltb_lt in H1, H2; lia.
Qed.

Lemma unit_of_bounds : forall a, 1 <= a <= p - 1 -> is_unit_b a = true.
Proof.
  intros a H; unfold is_unit_b; apply andb_true_iff; split; apply Nat.ltb_lt; lia.
Qed.

Lemma unit_ndiv : forall a, is_unit_b a = true -> ~ Nat.divide p a.
Proof. intros a H; apply unit_not_div, unit_bounds; exact H. Qed.

(* ---- multiplication on units (needs PRIMALITY) and residues ---- *)
Lemma umul_unit : forall u v : Up,
  is_unit_b ((proj1_sig u * proj1_sig v) mod p) = true.
Proof.
  intros [a Ha] [b Hb]; cbn.
  apply unit_of_bounds, mulmod_in_units;
    [ exact Hp | apply unit_ndiv; exact Ha | apply unit_ndiv; exact Hb ].
Qed.

Definition umul (u v : Up) : Up :=
  exist _ ((proj1_sig u * proj1_sig v) mod p) (umul_unit u v).

Lemma rmul_ltb : forall x y : Rp, ((proj1_sig x * proj1_sig y) mod p <? p) = true.
Proof.
  intros x y; apply Nat.ltb_lt, Nat.mod_upper_bound; pose proof p_ge2; lia.
Qed.

Definition rmul (x y : Rp) : Rp :=
  exist _ ((proj1_sig x * proj1_sig y) mod p) (rmul_ltb x y).

(* ---- the maps ---- *)
Lemma phi_unit' : forall r : Rp, proj1_sig r <> 0 -> is_unit_b (proj1_sig r) = true.
Proof.
  intros [x Hx] Hne; cbn in *. apply Nat.ltb_lt in Hx.
  apply unit_of_bounds; lia.
Qed.

Definition phi (r : Rp) : Adj Up :=
  match Nat.eq_dec (proj1_sig r) 0 with
  | left _ => AZero Up
  | right Hne => AElt Up (exist _ (proj1_sig r) (phi_unit' r Hne))
  end.

Lemma psi_zero : (0 <? p) = true.
Proof. apply Nat.ltb_lt; pose proof p_ge2; lia. Qed.

Lemma psi_unit : forall u : Up, (proj1_sig u <? p) = true.
Proof.
  intros [x Hx]; cbn; unfold is_unit_b in Hx; apply andb_true_iff in Hx.
  destruct Hx as [_ H2]; exact H2.
Qed.

Definition psi (a : Adj Up) : Rp :=
  match a with
  | AZero _ => exist _ 0 psi_zero
  | AElt _ u => exist _ (proj1_sig u) (psi_unit u)
  end.

(* ---- phi's behaviour, packaged (never unfold phi again) ---- *)
Lemma phi_eq_zero : forall r : Rp, proj1_sig r = 0 -> phi r = AZero Up.
Proof.
  intros r Hr; unfold phi;
    destruct (Nat.eq_dec (proj1_sig r) 0) as [_ | Hne]; [ reflexivity | congruence ].
Qed.

Lemma phi_eq_elt : forall (r : Rp) (h : is_unit_b (proj1_sig r) = true),
  proj1_sig r <> 0 -> phi r = AElt Up (exist _ (proj1_sig r) h).
Proof.
  intros r h Hne; unfold phi;
    destruct (Nat.eq_dec (proj1_sig r) 0) as [Hz | Hn2]; [ congruence | ].
  apply AElt_cong; cbn; reflexivity.
Qed.

(* ---- bijection ---- *)
Lemma psi_phi : forall r, psi (phi r) = r.
Proof.
  intros r; unfold phi; destruct (Nat.eq_dec (proj1_sig r) 0) as [Hz | Hne].
  - apply Rp_eq; cbn; symmetry; exact Hz.
  - apply Rp_eq; cbn; reflexivity.
Qed.

Lemma phi_psi : forall a, phi (psi a) = a.
Proof.
  intros [|u].
  - apply phi_eq_zero; reflexivity.
  - assert (Hu : is_unit_b (proj1_sig (psi (AElt Up u))) = true) by exact (proj2_sig u).
    assert (Hne : proj1_sig (psi (AElt Up u)) <> 0)
      by (pose proof (unit_bounds _ Hu); lia).
    rewrite (phi_eq_elt (psi (AElt Up u)) Hu Hne).
    apply AElt_cong; reflexivity.
Qed.

Lemma phi_bijective : Bijective phi.
Proof. exists psi; split; [ exact psi_phi | exact phi_psi ]. Qed.

(* ---- homomorphism: phi carries residue-mult to aop ---- *)
Lemma aop_zr : forall i, aop Up umul i (AZero Up) = AZero Up.
Proof. intros [|a]; reflexivity. Qed.

Lemma phi_hom : forall x y : Rp, phi (rmul x y) = aop Up umul (phi x) (phi y).
Proof.
  intros x y.
  destruct (Nat.eq_dec (proj1_sig x) 0) as [Hx0 | Hxn].
  - rewrite (phi_eq_zero x Hx0); cbn [aop].
    apply phi_eq_zero.
    change (proj1_sig (rmul x y)) with ((proj1_sig x * proj1_sig y) mod p).
    rewrite Hx0, Nat.mul_0_l, Nat.Div0.mod_0_l; reflexivity.
  - destruct (Nat.eq_dec (proj1_sig y) 0) as [Hy0 | Hyn].
    + rewrite (phi_eq_zero y Hy0), aop_zr.
      apply phi_eq_zero.
      change (proj1_sig (rmul x y)) with ((proj1_sig x * proj1_sig y) mod p).
      rewrite Hy0, Nat.mul_0_r, Nat.Div0.mod_0_l; reflexivity.
    + assert (Hux : is_unit_b (proj1_sig x) = true) by (apply (phi_unit' x); exact Hxn).
      assert (Huy : is_unit_b (proj1_sig y) = true) by (apply (phi_unit' y); exact Hyn).
      rewrite (phi_eq_elt x Hux Hxn), (phi_eq_elt y Huy Hyn); cbn [aop].
      assert (Habu : is_unit_b (proj1_sig (rmul x y)) = true).
      { unfold rmul; cbn [proj1_sig].
        exact (umul_unit (exist _ (proj1_sig x) Hux) (exist _ (proj1_sig y) Huy)). }
      assert (Habn : proj1_sig (rmul x y) <> 0).
      { intro Hc; apply unit_bounds in Habu; lia. }
      rewrite (phi_eq_elt (rmul x y) Habu Habn).
      apply AElt_cong; unfold rmul, umul; cbn; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM:  primality is zero-adjunction                     *)
(* ----------------------------------------------------------------- *)
Theorem zmod_prime_iso :
  Bijective phi
  /\ (forall x y : Rp, phi (rmul x y) = aop Up umul (phi x) (phi y)).
Proof. split; [ exact phi_bijective | exact phi_hom ]. Qed.

End ZmodPrime.

Print Assumptions zmod_prime_iso.

(* ================================================================= *)
(*  END ZmodMultMonoid.v  (Brick 3 core: (Z/p,x) ~= Adj((Z/p)^x) --    *)
(*  every nonzero residue mod a prime is a unit, so the multiplicative *)
(*  monoid is the unit group with an absorbing zero adjoined.)         *)
(* ================================================================= *)

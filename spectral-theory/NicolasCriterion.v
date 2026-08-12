(* ================================================================= *)
(*  NicolasCriterion.v                                                *)
(*                                                                    *)
(*  A PRIMORIAL-BASED REDUCTION OF THE RIEMANN HYPOTHESIS.            *)
(*                                                                    *)
(*  Nicolas (1983) proved that RH is EQUIVALENT to an elementary      *)
(*  looking inequality on primorials N_k = prod_{i<=k} p_i and        *)
(*  Euler totient phi:                                             *)
(*                                                                    *)
(*     RH  <->  forall k>=1,   N_k / phi(N_k)  >  e^gamma * ln ln N_k. *)
(*                                                                    *)
(*  The central object  N_k/phi(N_k) = prod_{p<=p_k} p/(p-1)         *)
(*  (equivalently phi(N_k)/N_k = prod (1 - 1/p)) is exactly the       *)
(*  density of reduced residues -- the classes primes must fall into  *)
(*  -- INSIDE a primorial.  That is the nature of prime               *)
(*  distributions within primorials.                                 *)
(*                                                                    *)
(*  ---------------------------------------------------------------- *)
(*  HONEST SCOPE.  This file builds the fully-reachable, AXIOM-CLEAN  *)
(*  ARITHMETIC side and STATES the criterion as an RH-equivalent.     *)
(*  Proved unconditionally (Qed, no new axioms):                     *)
(*    - phi_prime            : phi(p) = p-1          (p prime)        *)
(*    - phi_prod_primes       : phi(prod distinct primes) = prod(p-1) *)
(*    - reduced_residue_density : phi(N)/N = prod (1 - 1/p)           *)
(*    - primorial_over_phi    : N/phi(N) = prod p/(p-1)               *)
(*    - concrete primorial instances (by computation)                *)
(*                                                                    *)
(*  NOT proved here (the deferred analytic core, = RH):              *)
(*    - the constant e^gamma is left as an abstract real `egamma`     *)
(*      (its construction + Mertens third theorem are future work);  *)
(*    - the equivalence Nicolas <-> RH itself (the deep Nicolas         *)
(*      theorem, via the explicit formula / zero bounds) is only      *)
(*      STATED, as the Prop `Nicolas_equiv_RH`, never asserted true.  *)
(*    Unlike SpectralTripleRH.v, NO tautological axiom is introduced. *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Reals Lra.
Require Import Totient DirichletConv DirichletMult DirichletPPow.
Require Import PrimeFactorizationN PrimorialSpectralTheory.
Require Import ComplexField RiemannXiEntire CZeta.
Import ListNotations.
Local Open Scope nat_scope.

(* ================================================================= *)
(*  0.  The product of a list of naturals                            *)
(* ================================================================= *)

Definition prodl (l : list nat) : nat := fold_right Nat.mul 1 l.

Lemma prodl_cons : forall x l, prodl (x :: l) = x * prodl l.
Proof. reflexivity. Qed.

Lemma prodl_ge1 : forall l, Forall (fun q => 1 <= q) l -> 1 <= prodl l.
Proof.
  induction l as [|x l IH]; intro H; simpl; [ lia | ].
  inversion H as [| ? ? Hx Hl]; subst. specialize (IH Hl).
  apply Nat.le_trans with (x * 1); [ lia | apply Nat.mul_le_mono_l; exact IH ].
Qed.

Lemma primes_ge1 : forall ps,
  Forall (fun q => prime (Z.of_nat q)) ps -> Forall (fun q => 1 <= q) ps.
Proof.
  induction ps as [|q ps IH]; intro H; [ constructor | ].
  inversion H as [| ? ? Hq Hps]; subst.
  constructor; [ pose proof (prime_ge_2 _ Hq); lia | apply IH; exact Hps ].
Qed.

(* ================================================================= *)
(*  1.  phi(p) = p - 1  for a prime p                                *)
(* ================================================================= *)

Lemma phi_prime : forall p, prime (Z.of_nat p) -> phi p = p - 1.
Proof.
  intros p Hp. pose proof (prime_ge_2 _ Hp) as Hp2.
  pose proof (phi_ppow p 1 Hp ltac:(lia)) as H.
  rewrite Nat.pow_1_r in H.
  change (1 - 1)%nat with 0%nat in H. rewrite Nat.pow_0_r in H.
  unfold dphi in H.
  apply Nat2Z.inj. rewrite Nat2Z.inj_sub by lia. rewrite H. reflexivity.
Qed.

(* ================================================================= *)
(*  2.  Coprimality of a prime to a product of OTHER primes         *)
(* ================================================================= *)

(* nat divisibility lifts to Z *)
Lemma nat_div_Z : forall x y, Nat.divide x y -> (Z.of_nat x | Z.of_nat y).
Proof. intros x y [k Hk]; exists (Z.of_nat k); subst; rewrite Nat2Z.inj_mul; ring. Qed.

(* Z-coprimality of naturals descends to Nat.gcd = 1 *)
Lemma natgcd_of_relprime : forall a b,
  rel_prime (Z.of_nat a) (Z.of_nat b) -> Nat.gcd a b = 1.
Proof.
  intros a b H. destruct H as [Ha Hb Hg].
  pose proof (Hg (Z.of_nat (Nat.gcd a b)) (nat_div_Z _ _ (Nat.gcd_divide_l a b))
                                          (nat_div_Z _ _ (Nat.gcd_divide_r a b))) as Hd.
  apply Nat2Z.inj; change (Z.of_nat 1) with 1%Z.
  apply Z.divide_1_r_nonneg; [ apply Nat2Z.is_nonneg | exact Hd ].
Qed.

Lemma rel_prime_prodl : forall p ps,
  prime (Z.of_nat p) -> Forall (fun q => prime (Z.of_nat q)) ps -> ~ In p ps ->
  rel_prime (Z.of_nat p) (Z.of_nat (prodl ps)).
Proof.
  intros p ps Hp; induction ps as [|q ps' IH]; intros Hpr Hnin.
  - simpl. apply rel_prime_sym, rel_prime_1.
  - rewrite prodl_cons, Nat2Z.inj_mul.
    inversion Hpr as [| ? ? Hq Hpr']; subst.
    apply rel_prime_mult.
    + apply distinct_primes_coprime; [ exact Hp | exact Hq | ].
      intro Heq. apply Nat2Z.inj in Heq. subst q. apply Hnin; left; reflexivity.
    + apply IH; [ exact Hpr' | intro Hin; apply Hnin; right; exact Hin ].
Qed.

Lemma gcd_prime_prodl : forall p ps,
  prime (Z.of_nat p) -> Forall (fun q => prime (Z.of_nat q)) ps -> ~ In p ps ->
  Nat.gcd p (prodl ps) = 1.
Proof. intros; apply natgcd_of_relprime, rel_prime_prodl; assumption. Qed.

(* ================================================================= *)
(*  3.  phi(prod of distinct primes) = prod (p - 1)   [THE CORE]     *)
(* ================================================================= *)

Theorem phi_prod_primes : forall ps,
  NoDup ps -> Forall (fun p => prime (Z.of_nat p)) ps ->
  phi (prodl ps) = prodl (map (fun p => p - 1) ps).
Proof.
  destruct phi_mult as [_ Hmul].
  induction ps as [|p ps' IH]; intros Hnd Hpr.
  - vm_compute; reflexivity.
  - inversion Hnd  as [| ? ? Hnin Hnd']; subst.
    inversion Hpr  as [| ? ? Hp   Hpr']; subst.
    assert (Hp1 : 1 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
    assert (HP1 : 1 <= prodl ps') by (apply prodl_ge1, primes_ge1; exact Hpr').
    assert (Hg  : Nat.gcd p (prodl ps') = 1) by (apply gcd_prime_prodl; assumption).
    pose proof (Hmul p (prodl ps') Hp1 HP1 Hg) as Hmm. unfold dphi in Hmm.
    assert (Hstep : phi (p * prodl ps') = phi p * phi (prodl ps')).
    { apply Nat2Z.inj. rewrite Nat2Z.inj_mul. exact Hmm. }
    rewrite prodl_cons, Hstep, (phi_prime p Hp), (IH Hnd' Hpr').
    cbn [map]. rewrite prodl_cons. reflexivity.
Qed.

(* ================================================================= *)
(*  4.  Real forms: reduced-residue density and the N/phi ratio     *)
(* ================================================================= *)

Definition prodR (l : list R) : R := fold_right Rmult 1%R l.

Lemma prodR_cons : forall x l, prodR (x :: l) = (x * prodR l)%R.
Proof. reflexivity. Qed.

Lemma primes_ge2 : forall ps,
  Forall (fun q => prime (Z.of_nat q)) ps -> Forall (fun q => 2 <= q) ps.
Proof.
  induction ps as [|q ps IH]; intro H; [ constructor | ].
  inversion H as [| ? ? Hq Hps]; subst.
  constructor; [ pose proof (prime_ge_2 _ Hq); lia | apply IH; exact Hps ].
Qed.

Lemma one_lt_INR_ge2 : forall p, (2 <= p)%nat -> (1 < INR p)%R.
Proof.
  intros p Hp. apply Rlt_le_trans with (INR 2); [ simpl; lra | apply le_INR; lia ].
Qed.

Lemma INR_prodl : forall l, INR (prodl l) = prodR (map INR l).
Proof.
  induction l as [|x l IH]; [ reflexivity | ].
  rewrite prodl_cons, mult_INR. cbn [map]. rewrite prodR_cons, IH. reflexivity.
Qed.

Lemma INR_prodl_pred : forall ps,
  Forall (fun p => 1 <= p)%nat ps ->
  INR (prodl (map (fun p => p - 1)%nat ps)) = prodR (map (fun p => (INR p - 1)%R) ps).
Proof.
  induction ps as [|p ps IH]; intro H; [ reflexivity | ].
  inversion H as [| ? ? Hp Hps]; subst.
  cbn [map]. rewrite prodl_cons, mult_INR, prodR_cons.
  rewrite (minus_INR p 1) by lia. rewrite IH by exact Hps. reflexivity.
Qed.

Lemma prodR_map_INR_pos : forall l,
  Forall (fun p => 1 <= p)%nat l -> (0 < prodR (map INR l))%R.
Proof.
  induction l as [|x l IH]; intro H; [ simpl; lra | ].
  inversion H as [| ? ? Hx Hl]; subst.
  cbn [map]; rewrite prodR_cons.
  apply Rmult_lt_0_compat; [ apply lt_0_INR; lia | apply IH; exact Hl ].
Qed.

Lemma prodR_pred_pos : forall ps,
  Forall (fun p => 2 <= p)%nat ps -> (0 < prodR (map (fun p => (INR p - 1)%R) ps))%R.
Proof.
  induction ps as [|p ps IH]; intro H; [ simpl; lra | ].
  inversion H as [| ? ? Hp Hps]; subst.
  cbn [map]; rewrite prodR_cons.
  apply Rmult_lt_0_compat;
    [ pose proof (one_lt_INR_ge2 p Hp); lra | apply IH; exact Hps ].
Qed.

(* phi(N)/N = prod (1 - 1/p) : the density of reduced residues.       *)
Lemma prodR_pred_div : forall ps,
  Forall (fun p => 2 <= p)%nat ps ->
  (prodR (map (fun p => (INR p - 1)%R) ps) / prodR (map INR ps))%R
    = prodR (map (fun p => (1 - / INR p)%R) ps).
Proof.
  induction ps as [|p ps IH]; intro H; [ simpl; field | ].
  inversion H as [| ? ? Hp Hps]; subst.
  assert (Hp0 : (INR p <> 0)%R) by (apply not_0_INR; lia).
  assert (Hdr : (prodR (map INR ps) <> 0)%R)
    by (apply Rgt_not_eq, Rlt_gt, prodR_map_INR_pos;
        revert Hps; apply Forall_impl; intros; lia).
  cbn [map]; rewrite !prodR_cons, <- (IH Hps). field; split; assumption.
Qed.

Theorem reduced_residue_density : forall ps,
  NoDup ps -> Forall (fun p => prime (Z.of_nat p)) ps ->
  (INR (phi (prodl ps)) / INR (prodl ps))%R
    = prodR (map (fun p => (1 - / INR p)%R) ps).
Proof.
  intros ps Hnd Hpr.
  rewrite (phi_prod_primes ps Hnd Hpr),
          (INR_prodl_pred ps (primes_ge1 ps Hpr)), (INR_prodl ps).
  apply prodR_pred_div, primes_ge2; exact Hpr.
Qed.

(* N/phi(N) = prod p/(p-1) : the reciprocal, Nicolas's central object.*)
Lemma prodR_ratio_div : forall ps,
  Forall (fun p => 2 <= p)%nat ps ->
  (prodR (map INR ps) / prodR (map (fun p => (INR p - 1)%R) ps))%R
    = prodR (map (fun p => (INR p / (INR p - 1))%R) ps).
Proof.
  induction ps as [|p ps IH]; intro H; [ simpl; field | ].
  inversion H as [| ? ? Hp Hps]; subst.
  assert (Hp1 : (INR p - 1 <> 0)%R) by (pose proof (one_lt_INR_ge2 p Hp); lra).
  assert (Hdr : (prodR (map (fun p => (INR p - 1)%R) ps) <> 0)%R)
    by (apply Rgt_not_eq, Rlt_gt, prodR_pred_pos; exact Hps).
  cbn [map]; rewrite !prodR_cons, <- (IH Hps). field; split; assumption.
Qed.

Theorem primorial_over_phi : forall ps,
  NoDup ps -> Forall (fun p => prime (Z.of_nat p)) ps ->
  (INR (prodl ps) / INR (phi (prodl ps)))%R
    = prodR (map (fun p => (INR p / (INR p - 1))%R) ps).
Proof.
  intros ps Hnd Hpr.
  rewrite (phi_prod_primes ps Hnd Hpr),
          (INR_prodl_pred ps (primes_ge1 ps Hpr)), (INR_prodl ps).
  apply prodR_ratio_div, primes_ge2; exact Hpr.
Qed.

(* ================================================================= *)
(*  5.  Bridge: the concrete primorial IS the product of its primes  *)
(* ================================================================= *)

Lemma prodl_app : forall l1 l2, prodl (l1 ++ l2) = prodl l1 * prodl l2.
Proof.
  induction l1 as [|x l1 IH]; intro l2; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma primorial_eq_prodl : forall k, primorial k = prodl (primorial_primes k).
Proof.
  induction k as [|k IH].
  - reflexivity.
  - replace (primorial (S k)) with (primorial k * kth_prime (S k)) by reflexivity.
    unfold primorial_primes in *.
    rewrite seq_S, map_app, prodl_app, <- IH.
    replace (0 + S k)%nat with (S k) by lia.
    cbn [map prodl fold_right]. ring.
Qed.

(* Concrete instances (checked by computation), tying the abstract     *)
(* identities to the actual primorial 2,6,30,210,2310,...              *)
Example phi_primorial_val_3 :
  phi (primorial 3) = prodl (map (fun p => p - 1) (primorial_primes 3)).
Proof. vm_compute; reflexivity. Qed.

Example phi_primorial_val_4 :
  phi (primorial 4) = prodl (map (fun p => p - 1) (primorial_primes 4)).
Proof. vm_compute; reflexivity. Qed.

Example primorial_over_phi_val_4 :
  primorial 4 = 2310 /\ phi (primorial 4) = 480.
Proof. vm_compute; split; reflexivity. Qed.

(* ================================================================= *)
(*  D.  The Nicolas criterion, STATED as an RH-equivalent            *)
(* ================================================================= *)

(* e^gamma (Euler-Mascheroni), left abstract; its construction and    *)
(* Mertens third theorem are the deferred analytic input.            *)
Parameter egamma : R.

(* N_k/phi(N_k) > e^gamma * ln ln N_k,  the Nicolas inequality at k.   *)
Definition Nicolas_holds (k : nat) : Prop :=
  (INR (primorial k) / INR (phi (primorial k))
     > egamma * ln (ln (INR (primorial k))))%R.

Definition NicolasCriterion : Prop :=
  forall k, (1 <= k)%nat -> Nicolas_holds k.

(* RH on the completed zeta XiC -- this is definitionally the Prop      *)
(* spectral-theory/RiemannHypothesis.v calls RiemannHypothesis (every  *)
(* zero of XiC lies on Re = 1/2).  We restate it here on the same XiC   *)
(* object because that file shares its basename with                    *)
(* packages/GHS/RiemannHypothesis.v under the flat namespace.           *)
Definition RH_XiC : Prop :=
  forall z : C, XiC z = C0 -> Re z = (/ 2)%R.

(* Nicolas theorem (1983), STATED only -- this equivalence is the       *)
(* load-bearing analytic gap (explicit formula / zero bounds) and is    *)
(* NOT proved here.  It is a genuine Prop, never asserted true.         *)
Definition Nicolas_equiv_RH : Prop :=
  NicolasCriterion <-> RH_XiC.

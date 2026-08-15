(* ================================================================= *)
(*  Ell2Fock.v   (the bosonic Fock tower of the primon gas over l^2)     *)
(*                                                                    *)
(*  By unique factorisation the Fock space of the primon gas over the   *)
(*  prime modes IS l^2(N_{>=1}) itself:  an occupation vector (k_p)_p    *)
(*  (finitely supported) <-> the integer  n = prod_p p^{k_p}, i.e. the   *)
(*  basis vector  e n  of Ell2.  On this identification:                *)
(*                                                                    *)
(*   * per-prime NUMBER / occupation operator  N_p = diag(v_p n)         *)
(*        (v_p = p-adic valuation = occupation of mode p in state n),    *)
(*   * per-prime CREATION  a_p^dag : e_m |-> e_{p m}   (raise k_p),       *)
(*   * per-prime ANNIHILATION  a_p : e_n |-> e_{n/p}   (lower k_p),       *)
(*   * the shift relation  a_p a_p^dag = I  (creation is an isometry),   *)
(*   * distinct modes commute  a_p^dag a_q^dag = a_q^dag a_p^dag,        *)
(*   * the vacuum is  e_1  (the empty occupation, integer 1):            *)
(*        a_p e_1 = 0  and  N_p e_1 = 0.                                 *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (+ functional_extensionality). *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith FunctionalExtensionality.
Require Import Ell2 Ell2Operator Ell2Basis PadicValuation.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  the per-mode operators                                            *)
(* ------------------------------------------------------------------ *)

(* creation  a_p^dag : raises the occupation of mode p  (e_m |-> e_{p m}) *)
Definition crea (p : nat) (f : nat -> R) : nat -> R :=
  fun n => if Nat.eqb (n mod p)%nat 0 then f (n / p)%nat else 0.

(* annihilation  a_p : lowers the occupation of mode p  (e_n |-> e_{n/p}) *)
Definition anni (p : nat) (f : nat -> R) : nat -> R := fun n => f (p * n)%nat.

(* number / occupation operator of mode p : diagonal, eigenvalue v_p(n) *)
Definition Nop (p : nat) : (nat -> R) -> nat -> R :=
  Dmul (fun n => INR (vp (Z.of_nat p) (Z.of_nat n))).

(* ------------------------------------------------------------------ *)
(*  the number operator is diagonal with occupation eigenvalues        *)
(* ------------------------------------------------------------------ *)

Lemma Dmul_e : forall a i n, Dmul a (e i) n = (a i * e i n)%R.
Proof.
  intros a i n. unfold Dmul, e. destruct (Nat.eqb n i) eqn:E;
    [ apply Nat.eqb_eq in E; subst; ring | ring ].
Qed.

(* N_p e_i = v_p(i) * e_i : the occupation of mode p in the state i *)
Lemma Nop_eigen : forall p i n,
  Nop p (e i) n = (INR (vp (Z.of_nat p) (Z.of_nat i)) * e i n)%R.
Proof. intros p i n; unfold Nop; rewrite Dmul_e; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  creation shifts the basis :  a_p^dag e_m = e_{p m}                 *)
(* ------------------------------------------------------------------ *)

Lemma crea_e : forall p m, (1 <= p)%nat -> crea p (e m) = e (p * m).
Proof.
  intros p m Hp. apply functional_extensionality; intro n.
  unfold crea, e. destruct (Nat.eqb (n mod p) 0) eqn:E.
  - apply Nat.eqb_eq, Nat.mod_divide in E; [ | lia ]. destruct E as [k Hk]. subst n.
    rewrite Nat.div_mul by lia.
    destruct (Nat.eqb k m) eqn:E1, (Nat.eqb (k * p) (p * m)) eqn:E2; try reflexivity.
    + apply Nat.eqb_eq in E1; subst k; rewrite Nat.mul_comm, Nat.eqb_refl in E2; discriminate.
    + apply Nat.eqb_eq in E2; rewrite Nat.mul_comm in E2;
        apply Nat.mul_cancel_l in E2; [ | lia ]; subst k;
        rewrite Nat.eqb_refl in E1; discriminate.
  - destruct (Nat.eqb n (p * m)) eqn:E2; [ | reflexivity ].
    apply Nat.eqb_eq in E2; subst n.
    rewrite Nat.mul_comm, Nat.mod_mul in E by lia. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  the shift relation  a_p a_p^dag = I  (creation is an isometry)     *)
(* ------------------------------------------------------------------ *)

Lemma anni_crea_e : forall p m, (1 <= p)%nat -> anni p (crea p (e m)) = e m.
Proof.
  intros p m Hp. rewrite (crea_e p m Hp).
  apply functional_extensionality; intro n. unfold anni, e.
  destruct (Nat.eqb (p * n) (p * m)) eqn:E1, (Nat.eqb n m) eqn:E2; try reflexivity.
  - apply Nat.eqb_eq in E1; apply Nat.mul_cancel_l in E1; [ | lia ];
      subst n; rewrite Nat.eqb_refl in E2; discriminate.
  - apply Nat.eqb_eq in E2; subst n; rewrite Nat.eqb_refl in E1; discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  distinct modes are independent :  a_p^dag a_q^dag = a_q^dag a_p^dag *)
(* ------------------------------------------------------------------ *)

Lemma crea_crea_e : forall p q m, (1 <= p)%nat -> (1 <= q)%nat ->
  crea p (crea q (e m)) = crea q (crea p (e m)).
Proof.
  intros p q m Hp Hq.
  rewrite (crea_e q m Hq), (crea_e p (q * m) Hp).
  rewrite (crea_e p m Hp), (crea_e q (p * m) Hq).
  f_equal. lia.
Qed.

(* ------------------------------------------------------------------ *)
(*  the vacuum  e_1  (integer 1 = empty occupation)                    *)
(* ------------------------------------------------------------------ *)

(* annihilating any mode from the vacuum gives 0 *)
Lemma anni_vacuum : forall p, (2 <= p)%nat -> anni p (e 1) = (fun _ => 0).
Proof.
  intros p Hp. apply functional_extensionality; intro n. unfold anni, e.
  destruct (Nat.eqb (p * n) 1) eqn:E; [ | reflexivity ].
  apply Nat.eqb_eq in E. destruct n; [ rewrite Nat.mul_0_r in E; discriminate | ].
  nia.
Qed.

(* the vacuum has zero occupation in every mode *)
Lemma Nop_vacuum : forall p n, (2 <= p)%nat -> Nop p (e 1) n = 0.
Proof.
  intros p n Hp. rewrite Nop_eigen.
  replace (vp (Z.of_nat p) (Z.of_nat 1)) with 0%nat; [ simpl; ring | ].
  symmetry. unfold vp.
  replace (Z.of_nat 1) with 1%Z by reflexivity.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  cbn [vpf]. rewrite Z.mod_1_l by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  every operator keeps a basis vector inside l^2                     *)
(* ------------------------------------------------------------------ *)

(* annihilation on the basis :  a_p e_n = e_{n/p}  if p|n,  else 0 *)
Lemma anni_e : forall p n, (1 <= p)%nat ->
  anni p (e n) = (if Nat.eqb (n mod p) 0 then e (n / p) else (fun _ => 0)).
Proof.
  intros p n Hp. apply functional_extensionality; intro k. unfold anni, e.
  destruct (Nat.eqb (n mod p) 0) eqn:E.
  - apply Nat.eqb_eq, Nat.mod_divide in E; [ | lia ]. destruct E as [j Hj]. subst n.
    rewrite Nat.div_mul by lia.
    destruct (Nat.eqb (p * k) (j * p)) eqn:E1, (Nat.eqb k j) eqn:E2; try reflexivity.
    + apply Nat.eqb_eq in E1; rewrite Nat.mul_comm in E1;
        apply Nat.mul_cancel_r in E1; [ | lia ]; subst k;
        rewrite Nat.eqb_refl in E2; discriminate.
    + apply Nat.eqb_eq in E2; subst k;
        rewrite (Nat.mul_comm p j), Nat.eqb_refl in E1; discriminate.
  - destruct (Nat.eqb (p * k) n) eqn:E2; [ | reflexivity ].
    apply Nat.eqb_eq in E2; subst n.
    rewrite (Nat.mul_comm p k), Nat.mod_mul in E by lia. discriminate.
Qed.

Lemma Ell2_crea_e : forall p m, (1 <= p)%nat -> Ell2 (crea p (e m)).
Proof. intros p m Hp; rewrite (crea_e p m Hp); apply Ell2_e. Qed.

Lemma Ell2_anni_e : forall p n, (1 <= p)%nat -> Ell2 (anni p (e n)).
Proof.
  intros p n Hp. rewrite (anni_e p n Hp).
  destruct (Nat.eqb (n mod p) 0); [ apply Ell2_e | apply Ell2_zero ].
Qed.

Lemma Ell2_Nop_e : forall p i, Ell2 (Nop p (e i)).
Proof.
  intros p i.
  apply (Ell2_ext (fun n => INR (vp (Z.of_nat p) (Z.of_nat i)) * e i n)%R);
    [ intro n; symmetry; apply Nop_eigen | apply Ell2_scal, Ell2_e ].
Qed.

(* ------------------------------------------------------------------ *)
(*  bundle : the primon-gas bosonic Fock structure on l^2             *)
(* ------------------------------------------------------------------ *)

Theorem primon_fock_tower :
  (* number operator is diagonal with occupation eigenvalues *)
  (forall p i n, Nop p (e i) n = INR (vp (Z.of_nat p) (Z.of_nat i)) * e i n)
  (* creation raises the occupation of mode p *)
  /\ (forall p m, (1 <= p)%nat -> crea p (e m) = e (p * m))
  (* annihilation is a left inverse of creation (a_p is an isometry adjoint) *)
  /\ (forall p m, (1 <= p)%nat -> anni p (crea p (e m)) = e m)
  (* distinct modes are independent *)
  /\ (forall p q m, (1 <= p)%nat -> (1 <= q)%nat ->
        crea p (crea q (e m)) = crea q (crea p (e m)))
  (* the vacuum e_1 is annihilated by every mode *)
  /\ (forall p, (2 <= p)%nat -> anni p (e 1) = (fun _ => 0)).
Proof.
  repeat split.
  - apply Nop_eigen.
  - apply crea_e.
  - apply anni_crea_e.
  - apply crea_crea_e.
  - apply anni_vacuum.
Qed.

Print Assumptions primon_fock_tower.

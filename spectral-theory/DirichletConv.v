(* ================================================================= *)
(*  DirichletConv.v                                                  *)
(*                                                                    *)
(*  THE DIRICHLET CONVOLUTION RING of arithmetic functions ℕ → ℤ.    *)
(*                                                                    *)
(*  (f ∗ g)(n) = Σ_{d·e = n} f(d) g(e)  — convolution in the monoid   *)
(*  (ℕ_{>0}, ×), the number-theoretic sibling of the group-algebra    *)
(*  convolution.  Defined as an indicator double sum over [1,n], so   *)
(*  the proofs mirror the group algebra (commutativity by a Fubini    *)
(*  swap, etc.).                                                       *)
(*                                                                    *)
(*  This installment delivers: convolution is COMMUTATIVE, UNITAL      *)
(*  (identity ε(n)=[n=1]), and DISTRIBUTIVE over pointwise +; the      *)
(*  bridge to the standard divisor form (f ∗ g)(n) = Σ_{d∣n} f(d)      *)
(*  g(n/d); and the concrete arithmetic identity  φ ∗ 1 = id  (Euler's *)
(*  Σ_{d∣n} φ(d) = n, from Totient).  ASSOCIATIVITY (the remaining     *)
(*  ring axiom) and Möbius inversion are the next installment.  Closed *)
(*  under the global context (axiom-free).                            *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith Lia List.
Import ListNotations.
Require Import HopfGroupTensor Totient.
Open Scope Z_scope.

(* ================================================================= *)
(*  Extra finite-sum lemmas (on top of HopfGroupTensor's toolkit)     *)
(* ================================================================= *)
Lemma sumf_sift : forall (l : list nat) m g, NoDup l -> In m l ->
  sumf l (fun k => if (m =? k)%nat then g k else 0%Z) = g m.
Proof.
  induction l as [|a l IH]; intros m g Hnd Hin; [ inversion Hin | ].
  simpl; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (Nat.eqb_spec m a) as [->|Hne].
  - rewrite (sumf_ext l (fun k => if (a =? k)%nat then g k else 0%Z) (fun _ => 0%Z)).
    + rewrite sumf_zero; ring.
    + intros k Hk; destruct (Nat.eqb_spec a k) as [->|_];
        [ exfalso; apply Hna; exact Hk | reflexivity ].
  - destruct Hin as [->|Hin]; [ exfalso; apply Hne; reflexivity | ].
    rewrite IH by assumption; ring.
Qed.

Lemma sumf_single : forall (l : list nat) m h, NoDup l -> In m l ->
  (forall j, In j l -> j <> m -> h j = 0%Z) -> sumf l h = h m.
Proof.
  induction l as [|a l IH]; intros m h Hnd Hin Hz; [ inversion Hin | ].
  simpl; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (Nat.eq_dec a m) as [->|Hne].
  - rewrite (sumf_ext l h (fun _ => 0%Z)).
    + rewrite sumf_zero; ring.
    + intros j Hj; apply Hz; [ right; exact Hj | intro Heq; subst; contradiction ].
  - destruct Hin as [->|Hin]; [ contradiction | ].
    rewrite (Hz a (or_introl eq_refl) Hne), (IH m h Hnd' Hin); [ ring | ].
    intros j Hj Hjm; apply Hz; [ right; exact Hj | exact Hjm ].
Qed.

Lemma sumf_cons : forall (a : nat) l F, sumf (a :: l) F = F a + sumf l F.
Proof. reflexivity. Qed.

Lemma sumf_filter : forall (l : list nat) (p : nat -> bool) h,
  sumf l (fun k => if p k then h k else 0%Z) = sumf (filter p l) h.
Proof.
  induction l as [|a l IH]; intros p h; [ reflexivity | ].
  rewrite sumf_cons; cbn [filter]; destruct (p a) eqn:Ep.
  - rewrite sumf_cons, IH; reflexivity.
  - change (if false then h a else 0%Z) with 0%Z; rewrite IH; ring.
Qed.

Lemma sumf_ofnat : forall (l : list nat) (h : nat -> nat),
  sumf l (fun d => Z.of_nat (h d)) = Z.of_nat (fold_right Nat.add 0%nat (map h l)).
Proof.
  induction l as [|a l IH]; intros h; simpl; [ reflexivity | ].
  rewrite IH, Nat2Z.inj_add; reflexivity.
Qed.

(* ================================================================= *)
(*  The Dirichlet convolution and the arithmetic-function operations *)
(* ================================================================= *)
Definition dconv (f g : nat -> Z) (n : nat) : Z :=
  sumf (seq 1 n) (fun d => sumf (seq 1 n) (fun e => if (d * e =? n)%nat then f d * g e else 0)).

Definition deps : nat -> Z := fun n => if (n =? 1)%nat then 1 else 0.  (* identity ε *)
Definition done : nat -> Z := fun _ => 1.                              (* constant 1 *)
Definition did  : nat -> Z := fun n => Z.of_nat n.                     (* id(n) = n *)
Definition dphi : nat -> Z := fun n => Z.of_nat (phi n).               (* Euler φ *)

(* ================================================================= *)
(*  COMMUTATIVITY                                                     *)
(* ================================================================= *)
Theorem dconv_comm : forall f g n, dconv f g n = dconv g f n.
Proof.
  intros f g n; unfold dconv.
  rewrite (sumf_swap (seq 1 n) (seq 1 n) (fun d e => if (d * e =? n)%nat then f d * g e else 0)).
  apply sumf_ext; intros d _; apply sumf_ext; intros e _.
  rewrite (Nat.mul_comm e d); destruct (d * e =? n)%nat; ring.
Qed.

(* ================================================================= *)
(*  Bridge to the standard divisor form                              *)
(* ================================================================= *)
Theorem dconv_as_div : forall f g n, (1 <= n)%nat ->
  dconv f g n = sumf (divisors n) (fun d => f d * g (n / d)%nat).
Proof.
  intros f g n Hn; unfold dconv, divisors.
  rewrite <- sumf_filter.
  apply sumf_ext; intros d Hd; apply in_seq in Hd.
  destruct (Nat.eqb_spec (n mod d) 0) as [Hdvd|Hndvd].
  - apply Nat.Lcm0.mod_divide in Hdvd.
    assert (Hdn : (d * (n / d) = n)%nat).
    { destruct Hdvd as [k Hk]; rewrite Hk, Nat.div_mul by lia; lia. }
    rewrite (sumf_single (seq 1 n) (n / d)%nat (fun e => if (d * e =? n)%nat then f d * g e else 0)).
    + rewrite Hdn, Nat.eqb_refl; reflexivity.
    + apply seq_NoDup.
    + apply in_seq; split; nia.
    + intros e He Hend; apply in_seq in He.
      destruct (Nat.eqb_spec (d * e) n) as [E|]; [ | reflexivity ].
      exfalso; apply Hend; nia.
  - transitivity (sumf (seq 1 n) (fun _ : nat => 0%Z)); [ | apply sumf_zero ].
    apply sumf_ext; intros e _; destruct (Nat.eqb_spec (d * e) n) as [E|]; [ | reflexivity ].
    exfalso; apply Hndvd; apply Nat.Lcm0.mod_divide; exists e; rewrite <- E; ring.
Qed.

(* ================================================================= *)
(*  UNIT:  f ∗ ε = f = ε ∗ f   (on n ≥ 1)                            *)
(* ================================================================= *)
Theorem dconv_eps_r : forall f n, (1 <= n)%nat -> dconv f deps n = f n.
Proof.
  intros f n Hn; rewrite (dconv_as_div f deps n Hn).
  rewrite (sumf_single (divisors n) n (fun d => f d * deps (n / d)%nat)).
  - rewrite Nat.div_same by lia; unfold deps; simpl; ring.
  - apply divisors_nodup.
  - apply filter_In; split; [ apply in_seq; lia | rewrite Nat.Div0.mod_same; reflexivity ].
  - intros d Hd Hdn; apply filter_In in Hd; destruct Hd as [Hin Hmod].
    apply in_seq in Hin; apply Nat.eqb_eq in Hmod; apply Nat.Lcm0.mod_divide in Hmod.
    unfold deps; destruct (Nat.eqb_spec (n / d) 1) as [E|]; [ | ring ].
    exfalso; apply Hdn; destruct Hmod as [k Hk].
    assert (n / d = k)%nat by (rewrite Hk, Nat.div_mul; lia); nia.
Qed.

Theorem dconv_eps_l : forall f n, (1 <= n)%nat -> dconv deps f n = f n.
Proof. intros f n Hn; rewrite dconv_comm; apply dconv_eps_r; exact Hn. Qed.

(* ================================================================= *)
(*  DISTRIBUTIVITY over pointwise addition                           *)
(* ================================================================= *)
Theorem dconv_distrib_l : forall f g h n,
  dconv f (fun k => g k + h k) n = dconv f g n + dconv f h n.
Proof.
  intros f g h n; unfold dconv.
  rewrite <- sumf_add; apply sumf_ext; intros d _.
  rewrite <- sumf_add; apply sumf_ext; intros e _.
  destruct (d * e =? n)%nat; ring.
Qed.

Theorem dconv_distrib_r : forall f g h n,
  dconv (fun k => f k + g k) h n = dconv f h n + dconv g h n.
Proof.
  intros f g h n; unfold dconv.
  rewrite <- sumf_add; apply sumf_ext; intros d _.
  rewrite <- sumf_add; apply sumf_ext; intros e _.
  destruct (d * e =? n)%nat; ring.
Qed.

(* ================================================================= *)
(*  CONNECTION TO NUMBER THEORY:  φ ∗ 1 = id                          *)
(*  Euler's  Σ_{d∣n} φ(d) = n  (Totient.totient_divisor_sum) is a      *)
(*  Dirichlet-convolution identity.                                    *)
(* ================================================================= *)
Theorem phi_done_eq_id : forall n, (1 <= n)%nat -> dconv dphi done n = did n.
Proof.
  intros n Hn; rewrite (dconv_as_div dphi done n Hn); unfold done, did, dphi.
  transitivity (sumf (divisors n) (fun d => Z.of_nat (phi d))).
  - apply sumf_ext; intros d _; ring.
  - rewrite sumf_ofnat, (totient_divisor_sum n Hn); reflexivity.
Qed.

Print Assumptions dconv_comm.
Print Assumptions dconv_eps_r.
Print Assumptions dconv_distrib_l.
Print Assumptions dconv_as_div.
Print Assumptions phi_done_eq_id.

(* ================================================================= *)
(*  END DirichletConv.v (part 1)                                      *)
(*  Dirichlet convolution: commutative, unital (ε = [n=1]),           *)
(*  distributive; the divisor-form bridge; and φ ∗ 1 = id.  Closed     *)
(*  under the global context (axiom-free).  Associativity (the deep    *)
(*  ring axiom) + Möbius inversion are the next installment.          *)
(* ================================================================= *)

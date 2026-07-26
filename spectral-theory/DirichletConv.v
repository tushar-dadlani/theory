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
(*  Delivers the full COMMUTATIVE RING structure — commutative,        *)
(*  associative, unital (identity ε(n)=[n=1]), distributive over       *)
(*  pointwise + — the bridge to the standard divisor form              *)
(*  (f ∗ g)(n) = Σ_{d∣n} f(d) g(n/d), and the number-theory payoffs:   *)
(*  φ ∗ 1 = id (Euler), the Möbius function μ (defined by its          *)
(*  recurrence, so μ ∗ 1 = ε by construction), MÖBIUS INVERSION        *)
(*  (g = f ∗ 1 ⟹ f = g ∗ μ), and φ = id ∗ μ.  Closed under the        *)
(*  global context (axiom-free).                                      *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith Lia List Permutation Wf_nat.
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
(*  ASSOCIATIVITY                                                     *)
(*  Both associations equal the symmetric triple sum                  *)
(*     tri f g h n = Σ_{a·b·c = n} f(a) g(b) h(c).                    *)
(* ================================================================= *)
Lemma if_sumf : forall (b : bool) (l : list nat) (F : nat -> Z),
  (if b then sumf l F else 0%Z) = sumf l (fun x => if b then F x else 0%Z).
Proof. intros b l F; destruct b; [ reflexivity | symmetry; apply sumf_zero ]. Qed.

Lemma sumf_seq_extend : forall (h : nat -> Z) d n, (d <= n)%nat ->
  (forall k, (d < k <= n)%nat -> h k = 0%Z) ->
  sumf (seq 1 n) h = sumf (seq 1 d) h.
Proof.
  intros h d n Hdn Hz.
  replace n with (d + (n - d))%nat by lia.
  rewrite seq_app, sumf_app.
  replace (1 + d)%nat with (S d) by lia.
  rewrite (sumf_ext (seq (S d) (n - d)) h (fun _ => 0%Z)).
  - rewrite sumf_zero, Z.add_0_r; reflexivity.
  - intros k Hk; apply in_seq in Hk; apply Hz; lia.
Qed.

Lemma dconv_extend : forall f g d n, (1 <= d <= n)%nat ->
  dconv f g d =
  sumf (seq 1 n) (fun a => sumf (seq 1 n) (fun b => if (a * b =? d)%nat then f a * g b else 0)).
Proof.
  intros f g d n [Hd Hdn]; unfold dconv.
  rewrite (sumf_seq_extend
    (fun a => sumf (seq 1 n) (fun b => if (a * b =? d)%nat then f a * g b else 0)) d n Hdn).
  - apply sumf_ext; intros a Ha; apply in_seq in Ha.
    rewrite (sumf_seq_extend (fun b => if (a * b =? d)%nat then f a * g b else 0) d n Hdn).
    + reflexivity.
    + intros k Hk; destruct (Nat.eqb_spec (a * k) d) as [E|]; [ exfalso; nia | reflexivity ].
  - intros a Ha.
    transitivity (sumf (seq 1 n) (fun _ : nat => 0%Z)); [ | apply sumf_zero ].
    apply sumf_ext; intros b Hb; apply in_seq in Hb.
    destruct (Nat.eqb_spec (a * b) d) as [E|]; [ exfalso; nia | reflexivity ].
Qed.

Lemma sumf_collapse : forall n a e (V : Z), (1 <= e)%nat -> (1 <= n)%nat ->
  sumf (seq 1 n) (fun d => if (a =? d)%nat then (if (d * e =? n)%nat then V else 0) else 0)
  = (if (a * e =? n)%nat then V else 0).
Proof.
  intros n a e V He Hn.
  destruct (in_dec Nat.eq_dec a (seq 1 n)) as [Hin|Hnin].
  - rewrite (sumf_sift (seq 1 n) a (fun d => if (d * e =? n)%nat then V else 0));
      [ reflexivity | apply seq_NoDup | exact Hin ].
  - assert (Hae : (a * e =? n)%nat = false).
    { destruct (Nat.eqb_spec (a * e) n) as [E|]; [ | reflexivity ].
      exfalso; apply Hnin; apply in_seq; nia. }
    rewrite Hae.
    transitivity (sumf (seq 1 n) (fun _ : nat => 0%Z)); [ | apply sumf_zero ].
    apply sumf_ext; intros d Hd; destruct (Nat.eqb_spec a d) as [->|]; [ contradiction | reflexivity ].
Qed.

Definition tri (f g h : nat -> Z) (n : nat) : Z :=
  sumf (seq 1 n) (fun a => sumf (seq 1 n) (fun b => sumf (seq 1 n) (fun c =>
    if (a * b * c =? n)%nat then f a * g b * h c else 0))).

Lemma dconv_R_tri : forall f g h n, (1 <= n)%nat -> dconv f (dconv g h) n = tri f g h n.
Proof.
  intros f g h n Hn; unfold dconv at 1.
  transitivity (sumf (seq 1 n) (fun d => sumf (seq 1 n) (fun e =>
     sumf (seq 1 n) (fun b => sumf (seq 1 n) (fun c =>
       if (b * c =? e)%nat then (if (d * e =? n)%nat then f d * g b * h c else 0) else 0))))).
  { apply sumf_ext; intros d Hd; apply sumf_ext; intros e He; apply in_seq in He.
    assert (HAB : f d * dconv g h e
       = sumf (seq 1 n) (fun b => sumf (seq 1 n) (fun c => if (b * c =? e)%nat then f d * g b * h c else 0))).
    { rewrite (dconv_extend g h e n) by lia.
      rewrite <- sumf_scal; apply sumf_ext; intros b _.
      rewrite <- sumf_scal; apply sumf_ext; intros c _.
      destruct (b * c =? e)%nat; ring. }
    destruct (Nat.eqb_spec (d * e) n) as [Hde|Hde].
    - change (if true then f d * dconv g h e else 0%Z) with (f d * dconv g h e).
      rewrite HAB; apply sumf_ext; intros b _; apply sumf_ext; intros c _.
      destruct (b * c =? e)%nat; reflexivity.
    - change (if false then f d * dconv g h e else 0%Z) with 0%Z.
      symmetry; transitivity (sumf (seq 1 n) (fun _ : nat => 0%Z)); [ | apply sumf_zero ].
      apply sumf_ext; intros b _; transitivity (sumf (seq 1 n) (fun _ : nat => 0%Z)); [ | apply sumf_zero ].
      apply sumf_ext; intros c _; destruct (b * c =? e)%nat; reflexivity. }
  unfold tri.
  apply sumf_ext; intros d Hd; apply in_seq in Hd.
  rewrite (sumf_swap (seq 1 n) (seq 1 n)
     (fun e b => sumf (seq 1 n) (fun c =>
        if (b * c =? e)%nat then (if (d * e =? n)%nat then f d * g b * h c else 0) else 0))).
  apply sumf_ext; intros b Hb.
  rewrite (sumf_swap (seq 1 n) (seq 1 n)
     (fun e c => if (b * c =? e)%nat then (if (d * e =? n)%nat then f d * g b * h c else 0) else 0)).
  apply sumf_ext; intros c Hc.
  transitivity (sumf (seq 1 n) (fun e =>
     if (b * c =? e)%nat then (if (e * d =? n)%nat then f d * g b * h c else 0) else 0)).
  { apply sumf_ext; intros e _; rewrite (Nat.mul_comm d e); reflexivity. }
  rewrite (sumf_collapse n (b * c) d (f d * g b * h c) ltac:(lia) Hn).
  replace (b * c * d)%nat with (d * b * c)%nat by ring; reflexivity.
Qed.

Lemma tri_rot : forall f g h n, tri h f g n = tri f g h n.
Proof.
  intros f g h n; unfold tri.
  rewrite (sumf_swap (seq 1 n) (seq 1 n)
     (fun a b => sumf (seq 1 n) (fun c => if (a * b * c =? n)%nat then h a * f b * g c else 0))).
  apply sumf_ext; intros b Hb.
  rewrite (sumf_swap (seq 1 n) (seq 1 n)
     (fun a c => if (a * b * c =? n)%nat then h a * f b * g c else 0)).
  apply sumf_ext; intros c Hc; apply sumf_ext; intros a Ha.
  replace (a * b * c)%nat with (b * c * a)%nat by ring.
  destruct (b * c * a =? n)%nat; ring.
Qed.

Theorem dconv_assoc : forall f g h n, (1 <= n)%nat ->
  dconv (dconv f g) h n = dconv f (dconv g h) n.
Proof.
  intros f g h n Hn.
  rewrite dconv_comm, (dconv_R_tri h f g n Hn), tri_rot.
  symmetry; apply dconv_R_tri; exact Hn.
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

(* ================================================================= *)
(*  THE MÖBIUS FUNCTION and MÖBIUS INVERSION                          *)
(*  μ is defined by its recurrence Σ_{d∣n} μ(d) = [n=1], so μ ∗ 1 = ε  *)
(*  holds by construction.  Inversion then follows from the ring.     *)
(* ================================================================= *)
Definition properdivs (n : nat) : list nat := filter (fun d => (d <? n)%nat) (divisors n).

Lemma properdivs_nodup : forall n, NoDup (properdivs n).
Proof. intro n; apply NoDup_filter, divisors_nodup. Qed.

Fixpoint mu_f (fuel n : nat) : Z :=
  match fuel with
  | O => 0%Z
  | S f => (if (n =? 1)%nat then 1 else 0) - sumf (properdivs n) (mu_f f)
  end.
Definition mu (n : nat) : Z := mu_f n n.

Lemma mu_f_S : forall f n,
  mu_f (S f) n = (if (n =? 1)%nat then 1 else 0) - sumf (properdivs n) (mu_f f).
Proof. reflexivity. Qed.

Lemma mu_f_indep : forall n f, (n <= f)%nat -> mu_f f n = mu_f n n.
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf); intros f Hf.
  destruct f as [|f'].
  - assert (n = 0)%nat by lia; subst; reflexivity.
  - destruct n as [|n']; [ reflexivity | ].
    rewrite !mu_f_S; f_equal.
    apply sumf_ext; intros d Hd.
    unfold properdivs in Hd; rewrite filter_In, Nat.ltb_lt in Hd; destruct Hd as [_ Hlt].
    rewrite (IH d Hlt f'), (IH d Hlt n'); [ reflexivity | lia | lia ].
Qed.

Lemma mu_rec : forall n, (1 <= n)%nat -> mu n = deps n - sumf (properdivs n) mu.
Proof.
  intros n Hn; unfold mu at 1; destruct n as [|n']; [ lia | ].
  rewrite mu_f_S; unfold deps; f_equal.
  apply sumf_ext; intros d Hd.
  unfold properdivs in Hd; rewrite filter_In, Nat.ltb_lt in Hd; destruct Hd as [_ Hlt].
  unfold mu; apply mu_f_indep; lia.
Qed.

Lemma sumf_perm : forall (l l' : list nat) g, Permutation l l' -> sumf l g = sumf l' g.
Proof.
  intros l l' g H; induction H.
  - reflexivity.
  - rewrite !sumf_cons, IHPermutation; reflexivity.
  - rewrite !sumf_cons; ring.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma divisors_perm : forall n, (1 <= n)%nat -> Permutation (divisors n) (n :: properdivs n).
Proof.
  intros n Hn; apply NoDup_Permutation.
  - apply divisors_nodup.
  - constructor.
    + unfold properdivs; rewrite filter_In; intros [_ Hlt]; rewrite Nat.ltb_lt in Hlt; lia.
    + apply properdivs_nodup.
  - intros x; split.
    + intros Hx; pose proof Hx as Hx'; unfold divisors in Hx; rewrite filter_In in Hx.
      destruct Hx as [Hin _]; apply in_seq in Hin.
      destruct (Nat.eq_dec x n) as [->|Hne]; [ left; reflexivity | right ].
      unfold properdivs; rewrite filter_In; split; [ exact Hx' | rewrite Nat.ltb_lt; lia ].
    + intros [<-|Hx].
      * unfold divisors; rewrite filter_In; split;
          [ apply in_seq; lia | rewrite Nat.Div0.mod_same; reflexivity ].
      * unfold properdivs in Hx; rewrite filter_In in Hx; destruct Hx as [Hin _]; exact Hin.
Qed.

Lemma sumf_divisors_split : forall n g, (1 <= n)%nat ->
  sumf (divisors n) g = g n + sumf (properdivs n) g.
Proof.
  intros n g Hn.
  rewrite (sumf_perm (divisors n) (n :: properdivs n) g (divisors_perm n Hn)), sumf_cons; reflexivity.
Qed.

(* μ ∗ 1 = ε :  Σ_{d∣n} μ(d) = [n=1] *)
Theorem mu_one : forall n, (1 <= n)%nat -> dconv mu done n = deps n.
Proof.
  intros n Hn; rewrite (dconv_as_div mu done n Hn); unfold done.
  transitivity (sumf (divisors n) mu).
  - apply sumf_ext; intros d _; ring.
  - rewrite (sumf_divisors_split n mu Hn), (mu_rec n Hn); ring.
Qed.

(* dconv depends on its second argument only through [1,n] *)
Lemma dconv_ext_r : forall f g1 g2 n,
  (forall e, (1 <= e <= n)%nat -> g1 e = g2 e) -> dconv f g1 n = dconv f g2 n.
Proof.
  intros f g1 g2 n H; unfold dconv; apply sumf_ext; intros d Hd; apply in_seq in Hd.
  apply sumf_ext; intros e He; apply in_seq in He.
  destruct (d * e =? n)%nat; [ | reflexivity ]; rewrite (H e) by lia; reflexivity.
Qed.

(* MÖBIUS INVERSION:  g = f ∗ 1  ⟹  f = g ∗ μ *)
Theorem mobius_inversion : forall f g,
  (forall n, (1 <= n)%nat -> g n = dconv f done n) ->
  forall n, (1 <= n)%nat -> f n = dconv g mu n.
Proof.
  intros f g Hg n Hn.
  assert (Heq : dconv g mu n = dconv (dconv f done) mu n).
  { unfold dconv; apply sumf_ext; intros d Hd; apply in_seq in Hd.
    apply sumf_ext; intros e _; rewrite (Hg d) by lia; reflexivity. }
  rewrite Heq, dconv_assoc by exact Hn.
  rewrite <- (dconv_eps_r f n Hn) at 1.
  apply dconv_ext_r; intros e He.
  rewrite (dconv_comm done mu e), (mu_one e) by lia; reflexivity.
Qed.

(* φ = id ∗ μ :  φ(n) = Σ_{d∣n} μ(d)·(n/d) *)
Theorem phi_mobius : forall n, (1 <= n)%nat -> dphi n = dconv did mu n.
Proof. apply mobius_inversion; intros n Hn; symmetry; apply phi_done_eq_id; exact Hn. Qed.

Print Assumptions dconv_comm.
Print Assumptions dconv_assoc.
Print Assumptions dconv_eps_r.
Print Assumptions dconv_distrib_l.
Print Assumptions phi_done_eq_id.
Print Assumptions mu_one.
Print Assumptions mobius_inversion.
Print Assumptions phi_mobius.

(* ================================================================= *)
(*  END DirichletConv.v (part 1)                                      *)
(*  Dirichlet convolution: commutative, unital (ε = [n=1]),           *)
(*  distributive; the divisor-form bridge; and φ ∗ 1 = id.  Closed     *)
(*  under the global context (axiom-free).  Associativity (the deep    *)
(*  ring axiom) + Möbius inversion are the next installment.          *)
(* ================================================================= *)

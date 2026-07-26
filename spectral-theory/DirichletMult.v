(* ================================================================= *)
(*  DirichletMult.v                                                  *)
(*                                                                    *)
(*  MULTIPLICATIVITY of arithmetic functions, and in particular of    *)
(*  the Möbius function μ and Euler's totient φ.                     *)
(*                                                                    *)
(*  Core: the Dirichlet convolution of two multiplicative functions   *)
(*  is multiplicative (`dconv_mult`), resting on the coprime divisor   *)
(*  bijection divisors(mn) ↔ divisors(m)×divisors(n) (reused from      *)
(*  JacobiRHS.divisors_mul_perm).  From it:                            *)
(*    • μ is multiplicative — `mu_mult` (strong induction on the       *)
(*      product, using μ ∗ 1 = ε to cancel the sums);                 *)
(*    • φ is multiplicative — `phi_mult` (φ = id ∗ μ, both multipl.).  *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith Lia List Permutation Wf_nat.
Import ListNotations.
Require Import HopfGroupTensor Totient DirichletConv JacobiRHS R2Count.
Open Scope Z_scope.

(* ================================================================= *)
(*  Coprime divisor arithmetic                                       *)
(* ================================================================= *)
Lemma gcd_of_div : forall m n a b,
  Nat.gcd m n = 1%nat -> Nat.divide a m -> Nat.divide b n -> Nat.gcd a b = 1%nat.
Proof.
  intros m n a b Hco Ham Hbn.
  assert (Hd : Nat.divide (Nat.gcd a b) 1).
  { rewrite <- Hco; apply Nat.gcd_greatest;
      [ apply (Nat.divide_trans _ a); [ apply Nat.gcd_divide_l | exact Ham ]
      | apply (Nat.divide_trans _ b); [ apply Nat.gcd_divide_r | exact Hbn ] ]. }
  apply Nat.divide_1_r in Hd; exact Hd.
Qed.

Lemma div_divides : forall a m, (1 <= a)%nat -> Nat.divide a m -> Nat.divide (m / a) m.
Proof. intros a m Ha [k Hk]; exists a; rewrite Hk, Nat.div_mul by lia; ring. Qed.

Lemma gcd_div : forall m n a b, (1 <= a)%nat -> (1 <= b)%nat ->
  Nat.gcd m n = 1%nat -> Nat.divide a m -> Nat.divide b n -> Nat.gcd (m / a) (n / b) = 1%nat.
Proof.
  intros m n a b Ha Hb Hco Ham Hbn.
  apply (gcd_of_div m n); [ exact Hco | apply div_divides; assumption | apply div_divides; assumption ].
Qed.

Lemma divmul_div : forall m n a b, Nat.divide a m -> Nat.divide b n ->
  (1 <= a)%nat -> (1 <= b)%nat -> ((m * n) / (a * b) = (m / a) * (n / b))%nat.
Proof.
  intros m n a b [k Hk] [l Hl] Ha Hb.
  assert (Hma : (m / a = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
  assert (Hnb : (n / b = l)%nat) by (rewrite Hl, Nat.div_mul; lia).
  rewrite Hma, Hnb, Hk, Hl.
  replace (k * a * (l * b))%nat with (k * l * (a * b))%nat by ring.
  rewrite Nat.div_mul by nia; reflexivity.
Qed.

Lemma div_pos : forall a m, (1 <= a)%nat -> (1 <= m)%nat -> Nat.divide a m -> (1 <= m / a)%nat.
Proof. intros a m Ha Hm [k Hk]; rewrite Hk, Nat.div_mul by lia; nia. Qed.

(* ================================================================= *)
(*  Extra sum lemmas                                                  *)
(* ================================================================= *)
Lemma sumf_cons' : forall {T} (a : T) l F, sumf (a :: l) F = F a + sumf l F.
Proof. reflexivity. Qed.

Lemma sumf_sub : forall {T} (l : list T) f g,
  sumf l (fun k => f k - g k) = sumf l f - sumf l g.
Proof. intros T l f g; induction l as [|a l IH]; [ reflexivity | rewrite !sumf_cons', IH; ring ]. Qed.

Lemma sumf_sep : forall (l1 l2 : list nat) X Y,
  sumf l1 (fun a => sumf l2 (fun b => X a * Y b)) = sumf l1 X * sumf l2 Y.
Proof.
  intros l1 l2 X Y; transitivity (sumf l1 (fun a => X a * sumf l2 Y)).
  - apply sumf_ext; intros a _; apply sumf_scal.
  - apply sumf_mul_const_r.
Qed.

Lemma sumf_prodsep : forall (l1 l2 : list nat) X Y,
  sumf (list_prod l1 l2) (fun ab => X (fst ab) * Y (snd ab)) = sumf l1 X * sumf l2 Y.
Proof.
  intros l1 l2 X Y; rewrite sumf_list_prod; rewrite <- sumf_sep.
  apply sumf_ext; intros a _; apply sumf_ext; intros b _; cbn [fst snd]; reflexivity.
Qed.

Lemma sumf_single_gen : forall {T} (eqd : forall x y : T, {x = y} + {x <> y}) (l : list T) m h,
  NoDup l -> In m l -> (forall j, In j l -> j <> m -> h j = 0%Z) -> sumf l h = h m.
Proof.
  intros T eqd l m h; induction l as [|a l IH]; intros Hnd Hin Hz; [ inversion Hin | ].
  rewrite sumf_cons'; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (eqd a m) as [->|Hne].
  - rewrite (sumf_ext l h (fun _ => 0%Z)).
    + rewrite sumf_zero; ring.
    + intros j Hj; apply Hz; [ right; exact Hj | intro Heq; subst; contradiction ].
  - destruct Hin as [->|Hin]; [ contradiction | ].
    rewrite (Hz a (or_introl eq_refl) Hne), (IH Hnd' Hin); [ ring | ].
    intros j Hj Hjm; apply Hz; [ right; exact Hj | exact Hjm ].
Qed.

Lemma pair_eq_dec : forall x y : nat * nat, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Qed.

(* ================================================================= *)
(*  Multiplicative functions and the convolution                     *)
(* ================================================================= *)
Definition multiplicative (f : nat -> Z) : Prop :=
  f 1%nat = 1 /\
  forall m n, (1 <= m)%nat -> (1 <= n)%nat -> Nat.gcd m n = 1%nat -> f (m * n)%nat = f m * f n.

Lemma done_mult : multiplicative done.
Proof. split; [ reflexivity | intros; unfold done; ring ]. Qed.

Lemma did_mult : multiplicative did.
Proof.
  split; [ reflexivity | intros m n _ _ _; unfold did; rewrite Nat2Z.inj_mul; reflexivity ].
Qed.

Theorem dconv_mult : forall f g, multiplicative f -> multiplicative g -> multiplicative (dconv f g).
Proof.
  intros f g [Hf1 Hf] [Hg1 Hg]; split.
  - rewrite (dconv_as_div f g 1) by lia.
    replace (divisors 1) with (1 :: nil)%nat by reflexivity.
    rewrite sumf_cons, Nat.div_1_r, Hf1, Hg1; simpl; ring.
  - intros m n Hm Hn Hco.
    rewrite (dconv_as_div f g (m * n)) by nia.
    rewrite (sumf_perm _ _ _ (divisors_mul_perm m n Hco Hm Hn)), sumf_map, sumf_list_prod.
    transitivity (sumf (divisors m) (fun a => sumf (divisors n)
       (fun b => (f a * g (m / a)%nat) * (f b * g (n / b)%nat)))).
    { apply sumf_ext; intros a Ha; apply sumf_ext; intros b Hb; cbn [fst snd].
      apply in_divisors in Ha; apply in_divisors in Hb.
      destruct Ha as [[Ha1 Ha2] Hamod]; destruct Hb as [[Hb1 Hb2] Hbmod].
      apply Nat.Lcm0.mod_divide in Hamod; apply Nat.Lcm0.mod_divide in Hbmod.
      assert (Hmapos : (1 <= m / a)%nat) by (apply div_pos; assumption).
      assert (Hnbpos : (1 <= n / b)%nat) by (apply div_pos; assumption).
      rewrite (Hf a b Ha1 Hb1 (gcd_of_div m n a b Hco Hamod Hbmod)).
      rewrite (divmul_div m n a b Hamod Hbmod Ha1 Hb1).
      rewrite (Hg (m / a)%nat (n / b)%nat Hmapos Hnbpos (gcd_div m n a b Ha1 Hb1 Hco Hamod Hbmod)); ring. }
    rewrite sumf_sep, <- (dconv_as_div f g m Hm), <- (dconv_as_div f g n Hn); reflexivity.
Qed.

(* ================================================================= *)
(*  μ is multiplicative                                              *)
(* ================================================================= *)
Lemma mu_1 : mu 1%nat = 1.
Proof. reflexivity. Qed.

Lemma Sigma_mu_div : forall n, (1 <= n)%nat -> sumf (divisors n) mu = deps n.
Proof.
  intros n Hn; rewrite <- (mu_one n Hn), (dconv_as_div mu done n Hn); unfold done.
  apply sumf_ext; intros d _; ring.
Qed.

Lemma mu_mult_prod : forall m n, (1 <= m)%nat -> (1 <= n)%nat -> Nat.gcd m n = 1%nat ->
  mu (m * n)%nat = mu m * mu n.
Proof.
  intros m n; remember (m * n)%nat as p eqn:Hp; revert m n Hp.
  induction p as [p IH] using (well_founded_induction lt_wf); intros m n Hp Hm Hn Hco.
  subst p.
  destruct (Nat.eq_dec m 1) as [->|Hm1]; [ rewrite Nat.mul_1_l, mu_1; ring | ].
  destruct (Nat.eq_dec n 1) as [->|Hn1]; [ rewrite Nat.mul_1_r, mu_1; ring | ].
  set (L := list_prod (divisors m) (divisors n)).
  assert (Hsingle : sumf L (fun ab => mu (fst ab * snd ab)%nat - mu (fst ab) * mu (snd ab))
                    = mu (m * n)%nat - mu m * mu n).
  { rewrite (sumf_single_gen pair_eq_dec L (m, n)).
    - cbn [fst snd]; reflexivity.
    - unfold L; apply NoDup_list_prod; apply divisors_nodup.
    - unfold L; apply in_prod;
        apply in_divisors; (split; [ split; [ lia | lia ] | apply Nat.Div0.mod_same ]).
    - intros [a b] Hab Habne; cbn [fst snd].
      unfold L in Hab; apply in_prod_iff in Hab; destruct Hab as [Ha Hb].
      apply in_divisors in Ha; apply in_divisors in Hb.
      destruct Ha as [[Ha1 Ha2] Hamod]; destruct Hb as [[Hb1 Hb2] Hbmod].
      apply Nat.Lcm0.mod_divide in Hamod; apply Nat.Lcm0.mod_divide in Hbmod.
      assert (Hab_lt : (a * b < m * n)%nat).
      { destruct (Nat.eq_dec a m) as [->|Ea];
          [ destruct (Nat.eq_dec b n) as [->|Eb]; [ exfalso; apply Habne; reflexivity | nia ] | nia ]. }
      rewrite (IH (a * b)%nat Hab_lt a b eq_refl Ha1 Hb1 (gcd_of_div m n a b Hco Hamod Hbmod)); ring. }
  assert (Hab0 : sumf L (fun ab => mu (fst ab * snd ab)%nat) = 0).
  { unfold L; rewrite <- (sumf_map (list_prod (divisors m) (divisors n))
                            (fun ab => (fst ab * snd ab)%nat) mu).
    rewrite <- (sumf_perm (divisors (m * n)) _ mu (divisors_mul_perm m n Hco Hm Hn)).
    rewrite (Sigma_mu_div (m * n) ltac:(nia)); unfold deps.
    replace (m * n =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; nia); reflexivity. }
  assert (Hprod0 : sumf L (fun ab => mu (fst ab) * mu (snd ab)) = 0).
  { unfold L; rewrite (sumf_prodsep (divisors m) (divisors n) mu mu).
    rewrite (Sigma_mu_div m Hm), (Sigma_mu_div n Hn); unfold deps.
    replace (m =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia); ring. }
  rewrite sumf_sub, Hab0, Hprod0 in Hsingle; lia.
Qed.

Theorem mu_mult : multiplicative mu.
Proof. split; [ apply mu_1 | apply mu_mult_prod ]. Qed.

(* ================================================================= *)
(*  φ is multiplicative  (φ = id ∗ μ)                                *)
(* ================================================================= *)
Theorem phi_mult : multiplicative dphi.
Proof.
  split; [ reflexivity | ].
  intros m n Hm Hn Hco.
  rewrite (phi_mobius (m * n) ltac:(nia)), (phi_mobius m Hm), (phi_mobius n Hn).
  apply (proj2 (dconv_mult did mu did_mult mu_mult)); assumption.
Qed.

Print Assumptions dconv_mult.
Print Assumptions mu_mult.
Print Assumptions phi_mult.

(* ================================================================= *)
(*  END DirichletMult.v                                              *)
(*  Dirichlet convolution of multiplicatives is multiplicative; μ and *)
(*  φ are multiplicative.  Closed under the global context (axiom-free)*)
(* ================================================================= *)

(* ================================================================= *)
(*  GaussSum.v                                                       *)
(*                                                                    *)
(*  THE GAUSS SUM and its absolute value:  |g(chi)|^2 = p.            *)
(*                                                                    *)
(*  For a prime p, a primitive root g, and a NONPRINCIPAL Dirichlet    *)
(*  character chi = dchar p g a0 (0 < a0 < p-1), with additive root    *)
(*  zeta = w p (a p-th root of unity), the Gauss sum                   *)
(*                                                                    *)
(*      g(chi) = sum_{n=1}^{p-1} chi(n) * zeta^n                       *)
(*                                                                    *)
(*  satisfies  g(chi) * conj(g(chi)) = p  (a complex character sum     *)
(*  whose modulus squared is the integer p).                          *)
(*                                                                    *)
(*  Proof (classical): |g|^2 = sum_{a,b} chi(a)conj(chi(b)) zeta^a     *)
(*  conj(zeta)^b; reindex a = (b*c) mod p (units_perm) and use         *)
(*  chi(a)conj(chi(b)) = chi(c) (multiplicativity + |chi(b)|=1) and    *)
(*  zeta^a conj(zeta)^b = (zeta^c conj(zeta))^b = beta(c)^b; the inner  *)
(*  sum over b is p-1 if c=1 and -1 otherwise (geometric series of the  *)
(*  p-th roots), and sum_c chi(c) = 0 (nonprincipal) closes it to p.    *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via w / trig), like   *)
(*  the whole character layer.                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Reals Lra.
Require Import ZmodPStar ZmodOrder PrimitiveRoot DirichletModP DirichletLEuler
        ComplexField RootsOfUnity DFTInversion DFTConvolution.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(*  Finite sums over a list:  Sf f l = sum_{x in l} f x               *)
(* ================================================================= *)

Definition Sf (f : nat -> C) (l : list nat) : C := fold_right Cadd C0 (map f l).

Lemma Sf_empty : forall f, Sf f [] = C0.                 Proof. reflexivity. Qed.
Lemma Sf_cons  : forall f x l, Sf f (x :: l) = Cadd (f x) (Sf f l).  Proof. reflexivity. Qed.

Lemma Sf_zero : forall l, Sf (fun _ => C0) l = C0.
Proof. induction l as [|x l IH]; [ reflexivity | rewrite Sf_cons, IH; ring ]. Qed.

Lemma Sf_ext : forall f h l, (forall x, In x l -> f x = h x) -> Sf f l = Sf h l.
Proof.
  intros f h l H; induction l as [|x l IH]; [ reflexivity | ].
  rewrite !Sf_cons, (H x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy); reflexivity.
Qed.

Lemma Sf_add : forall f h l, Sf (fun x => Cadd (f x) (h x)) l = Cadd (Sf f l) (Sf h l).
Proof. intros f h l; induction l as [|x l IH]; [ unfold Sf; simpl; ring | rewrite !Sf_cons, IH; ring ]. Qed.

Lemma Sf_scale_l : forall c f l, Sf (fun x => Cmul c (f x)) l = Cmul c (Sf f l).
Proof. intros c f l; induction l as [|x l IH]; [ unfold Sf; simpl; ring | rewrite !Sf_cons, IH; ring ]. Qed.

Lemma Sf_scale_r : forall c f l, Sf (fun x => Cmul (f x) c) l = Cmul (Sf f l) c.
Proof. intros c f l; induction l as [|x l IH]; [ unfold Sf; simpl; ring | rewrite !Sf_cons, IH; ring ]. Qed.

Lemma Sf_prod : forall f h l1 l2,
  Cmul (Sf f l1) (Sf h l2) = Sf (fun a => Sf (fun b => Cmul (f a) (h b)) l2) l1.
Proof.
  intros f h l1 l2; induction l1 as [|a l1 IH]; [ unfold Sf; simpl; ring | ].
  rewrite (Sf_cons f a l1), (Sf_cons (fun a0 => Sf (fun b => Cmul (f a0) (h b)) l2) a l1).
  replace (Cmul (Cadd (f a) (Sf f l1)) (Sf h l2))
    with (Cadd (Cmul (f a) (Sf h l2)) (Cmul (Sf f l1) (Sf h l2))) by ring.
  rewrite IH, <- (Sf_scale_l (f a) h l2); reflexivity.
Qed.

Lemma Sf_swap : forall G l1 l2,
  Sf (fun a => Sf (fun b => G a b) l2) l1 = Sf (fun b => Sf (fun a => G a b) l1) l2.
Proof.
  intros G l1 l2; induction l1 as [|a l1 IH].
  - rewrite (Sf_empty (fun a => Sf (fun b => G a b) l2)).
    rewrite <- (Sf_zero l2); apply Sf_ext; intros b _; rewrite Sf_empty; reflexivity.
  - rewrite (Sf_cons (fun a0 => Sf (fun b => G a0 b) l2) a l1), IH, <- Sf_add.
    apply Sf_ext; intros b _; rewrite (Sf_cons (fun a0 => G a0 b) a l1); reflexivity.
Qed.

Lemma Sf_const : forall l, Sf (fun _ => C1) l = RtoC (INR (length l)).
Proof.
  induction l as [|x l IH]; [ reflexivity | ].
  rewrite Sf_cons, IH; simpl length; rewrite S_INR; apply Ceq; simpl; lra.
Qed.

Lemma Sf_reindex_mul : forall f b p, prime (Z.of_nat p) -> ~ Nat.divide p b ->
  Sf f (seq 1 (p - 1)) = Sf (fun x => f ((b * x) mod p)) (seq 1 (p - 1)).
Proof.
  intros f b p Hp Hb; unfold Sf.
  rewrite <- (map_map (fun x => (b * x) mod p) f).
  apply fold_Cadd_perm, Permutation_map, Permutation_sym, units_perm; assumption.
Qed.

(* conjugation distributes over Sf *)
Lemma Cconj_Sf : forall f l, Cconj (Sf f l) = Sf (fun x => Cconj (f x)) l.
Proof.
  intros f l; induction l as [|x l IH].
  - rewrite (Sf_empty f), (Sf_empty (fun x => Cconj (f x))); apply Ceq; simpl; ring.
  - rewrite (Sf_cons f x l), (Sf_cons (fun x0 => Cconj (f x0)) x l), Cconj_add, IH; reflexivity.
Qed.

(* ================================================================= *)
(*  Modulus of a product / power over the custom C                   *)
(* ================================================================= *)

Lemma Cnorm2_mul : forall a b, Cnorm2 (Cmul a b) = (Cnorm2 a * Cnorm2 b)%R.
Proof. intros a b; unfold Cnorm2, Cmul; simpl; ring. Qed.

Lemma Cnorm2_pow : forall a k, Cnorm2 a = 1%R -> Cnorm2 (Cpow a k) = 1%R.
Proof.
  intros a k H; induction k as [|k IH]; cbn [Cpow];
    [ unfold Cnorm2, C1; simpl; ring | rewrite Cnorm2_mul, H, IH; ring ].
Qed.

(* ================================================================= *)
(*  The Gauss sum, for a fixed prime p, primitive root g, char a0     *)
(* ================================================================= *)

Section GaussSum.

Variable p : nat.
Hypothesis Hp : prime (Z.of_nat p).
Variable g : nat.
Hypothesis Hg : 1 <= g <= p - 1.
Hypothesis Hord : ord p g = p - 1.
Variable a0 : nat.
Hypothesis Ha0 : 0 < a0 < p - 1.

Lemma Hp2 : 2 <= p.        Proof. destruct Hp as [Hgt _]; lia. Qed.
Lemma H0p : (0 < p)%nat.   Proof. pose proof Hp2; lia. Qed.

Definition beta (c : nat) : C := Cmul (Cpow (w p) c) (wc p).
Definition T (c : nat) : C := Sf (fun b => Cpow (beta c) b) (seq 1 (p - 1)).
Definition gauss : C := Sf (fun n => Cmul (dchar p g a0 n) (Cpow (w p) n)) (seq 1 (p - 1)).

(* --- roots-of-unity facts about beta --- *)

Lemma beta_pow_p : forall c, Cpow (beta c) p = C1.
Proof.
  intro c; unfold beta; rewrite Cpow_Cmul.
  rewrite <- Cpow_mul, (Nat.mul_comm c p), Cpow_mul, (w_pow_N p H0p), Cpow_C1.
  rewrite (wc_pow_N p H0p); ring.
Qed.

Lemma beta_1 : beta 1 = C1.
Proof. unfold beta; cbn [Cpow]; transitivity (Cmul (wc p) (w p)); [ ring | apply wc_w_1 ]. Qed.

Lemma beta_neq_1 : forall c, 2 <= c <= p - 1 -> beta c <> C1.
Proof.
  intros c Hc Heq; unfold beta in Heq.
  assert (Hcw : Cpow (w p) c = w p).
  { transitivity (Cmul (Cmul (Cpow (w p) c) (wc p)) (w p)).
    - transitivity (Cmul (Cpow (w p) c) (Cmul (wc p) (w p))).
      + rewrite (wc_w_1 p); ring.
      + ring.
    - rewrite Heq; ring. }
  assert (Hp1 : Cpow (w p) 1 = w p) by (cbn [Cpow]; ring).
  assert (c = 1) by (apply (w_pow_inj p c 1); [ lia | lia | rewrite Hcw, Hp1; reflexivity ]).
  lia.
Qed.

(* --- character facts --- *)

Lemma chi_mod : forall n, dchar p g a0 (n mod p) = dchar p g a0 n.
Proof. intro n; unfold dchar; rewrite !Nat.Div0.mod_mod; reflexivity. Qed.

Lemma chi_norm1 : forall n, 1 <= n <= p - 1 ->
  Cmul (dchar p g a0 n) (Cconj (dchar p g a0 n)) = C1.
Proof.
  intros n Hn.
  assert (Hd : dchar p g a0 n = Cpow (w (p - 1)) (a0 * dlog p g (n mod p))).
  { unfold dchar; replace (n mod p =? 0) with false;
      [ reflexivity | symmetry; apply Nat.eqb_neq; rewrite Nat.mod_small by lia; lia ]. }
  rewrite Hd, Cmul_conj, (Cnorm2_pow (w (p - 1)) _ (Cnorm2_w (p - 1))); reflexivity.
Qed.

Lemma char_sum_zero : Sf (dchar p g a0) (seq 1 (p - 1)) = C0.
Proof.
  pose proof (dirichlet_orthogonality p g a0 0 Hp Hg Hord (proj2 Ha0)
                ltac:(pose proof Hp2; lia)) as HO.
  replace (a0 =? 0) with false in HO by (symmetry; apply Nat.eqb_neq; lia).
  unfold Sf.
  rewrite (map_ext_in (dchar p g a0)
             (fun n => Cmul (dchar p g a0 n) (Cconj (dchar p g 0 n))) (seq 1 (p - 1))).
  - exact HO.
  - intros n Hn; apply in_seq in Hn.
    assert (Hd0 : dchar p g 0 n = C1).
    { unfold dchar; replace (n mod p =? 0) with false
        by (symmetry; apply Nat.eqb_neq; rewrite Nat.mod_small by lia; lia).
      rewrite Nat.mul_0_l; reflexivity. }
    rewrite Hd0; replace (Cconj C1) with C1 by (apply Ceq; simpl; ring); ring.
Qed.

(* --- the inner sum T c --- *)

Lemma T_1 : T 1 = RtoC (INR (p - 1)).
Proof.
  unfold T; rewrite beta_1.
  rewrite (Sf_ext (fun b => Cpow C1 b) (fun _ => C1) (seq 1 (p - 1)) (fun b _ => Cpow_C1 b)).
  rewrite Sf_const, length_seq; reflexivity.
Qed.

Lemma T_neq : forall c, 2 <= c <= p - 1 -> T c = Copp C1.
Proof.
  intros c Hc.
  assert (Hcsum : Csum (fun b => Cpow (beta c) b) p = C0)
    by (apply sum_pow_eq_0; [ apply beta_neq_1; exact Hc | apply beta_pow_p ]).
  assert (Hsplit : Csum (fun b => Cpow (beta c) b) p
                   = Cadd C1 (Sf (fun b => Cpow (beta c) b) (seq 1 (p - 1)))).
  { rewrite Csum_fold.
    assert (Hs0 : seq 0 p = 0 :: seq 1 (p - 1)).
    { replace p with (1 + (p - 1)) at 1 by lia; rewrite seq_app; reflexivity. }
    rewrite Hs0; unfold Sf; cbn [map fold_right Cpow]; reflexivity. }
  unfold T.
  replace (Sf (fun b => Cpow (beta c) b) (seq 1 (p - 1)))
    with (Cadd (Copp C1) (Cadd C1 (Sf (fun b => Cpow (beta c) b) (seq 1 (p - 1))))) by ring.
  rewrite <- Hsplit, Hcsum; ring.
Qed.

(* --- conjugate of the Gauss sum --- *)

Lemma gauss_conj_eq :
  Cconj gauss = Sf (fun b => Cmul (Cconj (dchar p g a0 b)) (Cpow (wc p) b)) (seq 1 (p - 1)).
Proof.
  unfold gauss; rewrite Cconj_Sf; apply Sf_ext; intros b _.
  rewrite Cconj_mul, <- Cconj_pow; unfold wc; reflexivity.
Qed.

(* --- the per-b reindex (the crux) --- *)

Lemma inner_reindex : forall b, 1 <= b <= p - 1 ->
  Sf (fun a => Cmul (Cmul (dchar p g a0 a) (Cpow (w p) a))
                    (Cmul (Cconj (dchar p g a0 b)) (Cpow (wc p) b))) (seq 1 (p - 1))
  = Sf (fun x => Cmul (dchar p g a0 x) (Cpow (beta x) b)) (seq 1 (p - 1)).
Proof.
  intros b Hb.
  assert (Hbnd : ~ Nat.divide p b) by (apply unit_not_div; lia).
  rewrite (Sf_reindex_mul (fun a => Cmul (Cmul (dchar p g a0 a) (Cpow (w p) a))
                                         (Cmul (Cconj (dchar p g a0 b)) (Cpow (wc p) b)))
                          b p Hp Hbnd).
  apply Sf_ext; intros x Hx; apply in_seq in Hx.
  rewrite chi_mod, (dchar_mul p g a0 b x Hp Hg Hord).
  assert (Hzeta : Cpow (w p) ((b * x) mod p) = Cpow (Cpow (w p) x) b)
    by (rewrite <- (Cpow_w_mod p (b * x) H0p), (Nat.mul_comm b x), Cpow_mul; reflexivity).
  rewrite Hzeta.
  transitivity (Cmul (Cmul (dchar p g a0 b) (Cconj (dchar p g a0 b)))
                     (Cmul (dchar p g a0 x) (Cpow (beta x) b))).
  - unfold beta; rewrite Cpow_Cmul; ring.
  - rewrite (chi_norm1 b ltac:(lia)); ring.
Qed.

(* --- the double sum reduces to sum_c chi(c) T(c) --- *)

Lemma gauss_sq_reindex :
  Cmul gauss (Cconj gauss) = Sf (fun c => Cmul (dchar p g a0 c) (T c)) (seq 1 (p - 1)).
Proof.
  transitivity (Sf (fun b => Sf (fun x => Cmul (dchar p g a0 x) (Cpow (beta x) b)) (seq 1 (p - 1)))
                   (seq 1 (p - 1))).
  - rewrite gauss_conj_eq; unfold gauss; rewrite Sf_prod, Sf_swap.
    apply Sf_ext; intros b Hb; apply in_seq in Hb; apply inner_reindex; lia.
  - rewrite Sf_swap; apply Sf_ext; intros x _; unfold T; apply Sf_scale_l.
Qed.

(* --- the assembly: |g|^2 = p --- *)

Lemma gauss_abs : Cmul gauss (Cconj gauss) = RtoC (INR p).
Proof.
  assert (Hseq : seq 1 (p - 1) = 1 :: seq 2 (p - 2)) by (replace (p - 1) with (S (p - 2)) by lia; reflexivity).
  assert (Hrest : Sf (dchar p g a0) (seq 2 (p - 2)) = Copp C1).
  { pose proof char_sum_zero as HC.
    rewrite Hseq, Sf_cons, (dchar_1 p g a0 Hp Hg Hord) in HC.
    replace (Sf (dchar p g a0) (seq 2 (p - 2)))
      with (Cadd (Copp C1) (Cadd C1 (Sf (dchar p g a0) (seq 2 (p - 2))))) by ring.
    rewrite HC; ring. }
  rewrite gauss_sq_reindex, Hseq, Sf_cons.
  rewrite (dchar_1 p g a0 Hp Hg Hord), T_1.
  rewrite (Sf_ext (fun c => Cmul (dchar p g a0 c) (T c))
                  (fun c => Cmul (dchar p g a0 c) (Copp C1)) (seq 2 (p - 2)))
    by (intros c Hc; apply in_seq in Hc; rewrite (T_neq c ltac:(lia)); reflexivity).
  rewrite Sf_scale_r, Hrest.
  replace (Cadd (Cmul C1 (RtoC (INR (p - 1)))) (Cmul (Copp C1) (Copp C1)))
    with (Cadd (RtoC (INR (p - 1))) C1) by ring.
  replace C1 with (RtoC 1) by reflexivity.
  rewrite <- RtoC_add; f_equal.
  rewrite <- (S_INR (p - 1)); f_equal; pose proof Hp2; lia.
Qed.

End GaussSum.

(* ================================================================= *)
(*  MASTER: |g(chi)|^2 = p for a nonprincipal character mod p         *)
(* ================================================================= *)

Theorem gauss_sum_abs : forall p, prime (Z.of_nat p) ->
  forall a0, 0 < a0 < p - 1 ->
  exists g, 1 <= g <= p - 1 /\ ord p g = p - 1 /\
    Cmul (gauss p g a0) (Cconj (gauss p g a0)) = RtoC (INR p).
Proof.
  intros p Hp a0 Ha0; destruct (units_cyclic p Hp) as [g [Hg Hord]].
  exists g; repeat split; [ lia | lia | exact Hord | ].
  apply (gauss_abs p Hp g Hg Hord a0 Ha0).
Qed.

Print Assumptions gauss_sum_abs.

(* ================================================================= *)
(*  END GaussSum.v                                                   *)
(*  |g(chi)|^2 = p for a nonprincipal Dirichlet character mod a prime  *)
(*  p: a complex character sum whose modulus squared is the integer p, *)
(*  via the multiplicative reindex a=(b*c) mod p, |chi|=1, the         *)
(*  geometric series of the p-th roots (beta), and sum_c chi(c)=0.     *)
(*  Uses the classical Reals axioms (quarantined, via w/trig).        *)
(* ================================================================= *)

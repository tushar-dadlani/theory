(* ================================================================= *)
(*  CLPrincipal.v  --  L(s,chi_0) = (1 - p^{-s}) zeta(s)  on Re s > 1.*)
(*                                                                    *)
(*  The principal character is the one CLHolo1.LFun excludes by        *)
(*  construction (HA : 0 < A < p-1), and it is the one that carries    *)
(*  the pole: as s -> 1+, zeta blows up and 1 - p^{-s} does not        *)
(*  vanish, so L(s,chi_0) -> infinity.  That divergence is what makes  *)
(*  Dirichlet's theorem work, with every non-principal chi staying     *)
(*  bounded because L(1,chi) <> 0 (LFunOne).                           *)
(*                                                                    *)
(*  PROVED BY REUSING cdirichlet_product, NOT BY REINDEXING.  The      *)
(*  naive route is sum_{p | n} n^{-s} = p^{-s} zeta(s), which needs a  *)
(*  sub-series reindexing.  But the Euler factor IS a Dirichlet series *)
(*  -- efac, supported on {1, p} with values 1 and -p^{-s} -- and      *)
(*                                                                    *)
(*      (efac * 1)(n) = n^{-s} - [p | n] p^{-s} (n/p)^{-s}            *)
(*                    = n^{-s} (1 - [p | n])  =  chi_0(n) n^{-s}      *)
(*                                                                    *)
(*  so the whole thing is one application of the Dirichlet product,    *)
(*  with the ZETA side supplied verbatim by CVonMangoldtZeta.bterm_cv  *)
(*  and bterm_abs_cv.  The only new ingredient is summing a function   *)
(*  supported on two points of a NoDup list.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CPowMul CSeries CListSum
        CDirichlet CDirichletProduct CZetaTerm CZeta RealMobius Totient
        VonMangoldtGlobal CVonMangoldtZeta RootsOfUnity ZmodOrder
        DirichletModP CTwistedCoeff CLSeries.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- summing a two-point-supported function over a list.      *)
(* ----------------------------------------------------------------- *)

Lemma Cls_support1 : forall (l : list nat) (f : nat -> C) a,
  NoDup l -> In a l -> (forall x, In x l -> x <> a -> f x = C0) ->
  Cls l f = f a.
Proof.
  induction l as [| y l IH]; intros f a Hnd Hin Hz; [ destruct Hin | ].
  inversion Hnd as [| y' l' Hyn Hnd' ]; subst.
  rewrite Cls_cons. destruct (Nat.eq_dec y a) as [-> | Hne].
  - replace (Cls l f) with C0.
    2:{ symmetry. rewrite (Cls_ext nat f (fun _ => C0) l).
        - clear. induction l as [| z l IH]; [ reflexivity | ].
          rewrite Cls_cons, IH. apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring.
        - intros x Hx. apply Hz; [ right; exact Hx | ].
          intro E; subst x; contradiction. }
    apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring.
  - rewrite (Hz y (or_introl eq_refl) Hne).
    rewrite (IH f a Hnd' (match Hin with
                          | or_introl E => match Hne E with end
                          | or_intror H => H end)
               (fun x Hx => Hz x (or_intror Hx))).
    apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring.
Qed.

Lemma Cls_support2 : forall (l : list nat) (f : nat -> C) a b,
  NoDup l -> In a l -> In b l -> a <> b ->
  (forall x, In x l -> x <> a -> x <> b -> f x = C0) ->
  Cls l f = Cadd (f a) (f b).
Proof.
  induction l as [| y l IH]; intros f a b Hnd Ha Hb Hab Hz; [ destruct Ha | ].
  inversion Hnd as [| y' l' Hyn Hnd' ]; subst.
  rewrite Cls_cons.
  destruct (Nat.eq_dec y a) as [Eya | Hya].
  - subst y.
    assert (Hbl : In b l)
      by (destruct Hb as [E | H];
          [ exfalso; apply Hab; exact E | exact H ]).
    rewrite (Cls_support1 l f b Hnd' Hbl); [ reflexivity | ].
    intros x Hx Hxb. apply (Hz x (or_intror Hx)); [ | exact Hxb ].
    intro E; subst x; contradiction.
  - destruct (Nat.eq_dec y b) as [Eyb | Hyb].
    + subst y.
      assert (Hal : In a l)
        by (destruct Ha as [E | H]; [ exfalso; apply Hya; exact E | exact H ]).
      rewrite (Cls_support1 l f a Hnd' Hal).
      * apply Ceq; unfold Cadd; cbn [Re Im]; ring.
      * intros x Hx Hxa. apply (Hz x (or_intror Hx) Hxa).
        intro E; subst x; contradiction.
    + rewrite (Hz y (or_introl eq_refl) Hya Hyb).
      assert (Hal : In a l)
        by (destruct Ha as [E | H]; [ exfalso; apply Hya; exact E | exact H ]).
      assert (Hbl : In b l)
        by (destruct Hb as [E | H]; [ exfalso; apply Hyb; exact E | exact H ]).
      rewrite (IH f a b Hnd' Hal Hbl Hab (fun x Hx => Hz x (or_intror Hx))).
      apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring.
Qed.

Lemma Rls_support2 : forall (l : list nat) (f : nat -> R) a b,
  NoDup l -> In a l -> In b l -> a <> b ->
  (forall x, In x l -> x <> a -> x <> b -> f x = 0) ->
  Rls l f = f a + f b.
Proof.
  intros l f a b Hnd Ha Hb Hab Hz.
  assert (HC : Cls l (fun x => RtoC (f x)) = Cadd (RtoC (f a)) (RtoC (f b))).
  { apply (Cls_support2 l (fun x => RtoC (f x)) a b); try assumption.
    intros x Hx Hxa Hxb. rewrite (Hz x Hx Hxa Hxb).
    apply Ceq; unfold RtoC, C0; cbn [Re Im]; ring. }
  rewrite Cls_RtoC in HC. apply (f_equal Re) in HC.
  unfold RtoC, Cadd in HC; cbn [Re] in HC. exact HC.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the principal character, explicitly.                     *)
(* ----------------------------------------------------------------- *)

Lemma dchar0_val : forall p g n,
  dchar p g 0 n = if (n mod p =? 0)%nat then C0 else C1.
Proof.
  intros p g n. unfold dchar. destruct (n mod p =? 0)%nat; [ reflexivity | ].
  rewrite Nat.mul_0_l. reflexivity.
Qed.

Section Principal.

Variable p g : nat.
Hypothesis Hp2 : (2 <= p)%nat.
Variable s : C.
Hypothesis Hs : 1 < Re s.

Definition efac (d : nat) : C :=
  if (d =? 1)%nat then C1
  else if (d =? p)%nat then Copp (Cpw (INR p) (Copp s)) else C0.

Lemma efac_off : forall x, x <> 1%nat -> x <> p -> efac x = C0.
Proof.
  intros x H1 Hp. unfold efac.
  replace (x =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; exact H1).
  replace (x =? p)%nat with false by (symmetry; apply Nat.eqb_neq; exact Hp).
  reflexivity.
Qed.

Lemma efac_1 : efac 1%nat = C1.
Proof. unfold efac. reflexivity. Qed.

Lemma efac_p : efac p = Copp (Cpw (INR p) (Copp s)).
Proof.
  unfold efac.
  replace (p =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma efac_sum : forall N, (p <= N)%nat ->
  Cls (seq 1 N) efac = Cminus C1 (Cpw (INR p) (Copp s)).
Proof.
  intros N HN.
  rewrite (Cls_support2 (seq 1 N) efac 1%nat p (seq_NoDup N 1)).
  - rewrite efac_1, efac_p. apply Ceq; unfold Cadd, Cminus, Copp; cbn [Re Im]; ring.
  - apply in_seq; lia.
  - apply in_seq; lia.
  - lia.
  - intros x _ H1 Hpx. apply efac_off; assumption.
Qed.

Lemma efac_cv : CUn_cv (fun N => Cls (seq 1 N) efac)
                       (Cminus C1 (Cpw (INR p) (Copp s))).
Proof.
  intros eps He. exists p. intros N HN.
  rewrite (efac_sum N HN).
  replace (Cminus (Cminus C1 (Cpw (INR p) (Copp s)))
                  (Cminus C1 (Cpw (INR p) (Copp s)))) with C0
    by (apply Ceq; unfold Cminus, Cadd, Copp, C0; cbn [Re Im]; ring).
  rewrite (proj2 (Cmod0 C0) eq_refl). exact He.
Qed.

Lemma efac_abs_cv :
  { T | Un_cv (fun N => Rls (seq 1 N) (fun d => Cmod (efac d))) T }.
Proof.
  exists (Cmod C1 + Cmod (Copp (Cpw (INR p) (Copp s)))).
  intros eps He. exists p. intros N HN.
  assert (H1in : In 1%nat (seq 1 N)) by (rewrite in_seq; lia).
  assert (Hpin : In p (seq 1 N)) by (rewrite in_seq; lia).
  assert (Hne : 1%nat <> p) by lia.
  rewrite (Rls_support2 (seq 1 N) (fun d => Cmod (efac d)) 1%nat p
             (seq_NoDup N 1) H1in Hpin Hne).
  - rewrite efac_1, efac_p. unfold R_dist.
    replace (Cmod C1 + Cmod (Copp (Cpw (INR p) (Copp s)))
             - (Cmod C1 + Cmod (Copp (Cpw (INR p) (Copp s))))) with 0 by ring.
    rewrite Rabs_R0. exact He.
  - intros x _ H1 Hpx. rewrite (efac_off x H1 Hpx).
    apply (proj2 (Cmod0 C0) eq_refl).
Qed.

(* ---- the convolution collapses to the principal character ---- *)

Lemma efac_conv : forall n, (1 <= n)%nat ->
  Cls (divisors n) (fun d => Cmul (efac d) (bterm s (n / d)%nat))
  = Cmul (dchar p g 0 n) (bterm s n).
Proof.
  intros n Hn. rewrite dchar0_val.
  destruct (n mod p =? 0)%nat eqn:E.
  - (* p | n : the two terms cancel *)
    assert (Hd : Nat.divide p n).
    { apply (proj1 (Nat.Lcm0.mod_divide n p)). apply Nat.eqb_eq. exact E. }
    assert (Hpn : (p <= n)%nat) by (apply Nat.divide_pos_le; [ lia | exact Hd ]).
    assert (Hpin : In p (divisors n)) by (rewrite in_divisors; split; [ lia | exact Hd ]).
    assert (Hne : 1%nat <> p) by lia.
    rewrite (Cls_support2 (divisors n) _ 1%nat p (divisors_nodup n)
               (in_1_divisors n Hn) Hpin Hne).
    2:{ intros x _ H1 Hpx. rewrite (efac_off x H1 Hpx).
        apply Ceq; unfold Cmul, C0; cbn [Re Im]; ring. }
    rewrite efac_1, efac_p, Nat.div_1_r.
    assert (Hdd : (p * (n / p))%nat = n)
      by (destruct Hd as [q Hq]; rewrite Hq, Nat.div_mul by lia; lia).
    assert (Hq1 : (1 <= n / p)%nat)
      by (pose proof (Nat.div_mod_eq n p); nia).
    assert (Hsplit : Cmul (Cpw (INR p) (Copp s)) (bterm s (n / p)%nat) = bterm s n).
    { unfold bterm, gC. rewrite <- Cpw_base_mul by (apply lt_0_INR; lia).
      rewrite <- mult_INR. f_equal. f_equal. exact Hdd. }
    rewrite <- Hsplit. apply Ceq; unfold Cmul, Cadd, Copp, C1, C0; cbn [Re Im]; ring.
  - (* p does not divide n : only d = 1 survives *)
    rewrite (Cls_support1 (divisors n) _ 1%nat (divisors_nodup n)
               (in_1_divisors n Hn)).
    + rewrite efac_1, Nat.div_1_r.
      apply Ceq; unfold Cmul, C1; cbn [Re Im]; ring.
    + intros x Hx H1.
      assert (Hxp : x <> p).
      { intro Ex; subst x. apply in_divisors in Hx. destruct Hx as [_ Hdvd].
        assert (n mod p = 0)%nat
          by (apply (proj2 (Nat.Lcm0.mod_divide n p)); exact Hdvd).
        rewrite H in E. discriminate. }
      rewrite (efac_off x H1 Hxp).
      apply Ceq; unfold Cmul, C0; cbn [Re Im]; ring.
Qed.

(* ---- THE identity ---- *)

Theorem L0_eq_zeta_factor : forall (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  CUn_cv (fun N => Cls (seq 1 N) (fun n => Cmul (dchar p g 0 n) (bterm s n)))
         (Cmul (Cminus C1 (Cpw (INR p) (Copp s))) (zetaC s H0 H1)).
Proof.
  intros H0 H1.
  destruct efac_abs_cv as [TA HTA].
  destruct (bterm_abs_cv s Hs) as [TB HTB].
  pose proof (cdirichlet_product efac (bterm s)
                (Cminus C1 (Cpw (INR p) (Copp s))) (zetaC s H0 H1) TA TB
                efac_cv (bterm_cv s H0 H1 Hs) HTA HTB) as Hcp.
  apply (CUn_cv_ext (fun N => Cls (seq 1 N)
           (fun n => Cls (divisors n)
              (fun d => Cmul (efac d) (bterm s (n / d)%nat)))));
    [ | exact Hcp ].
  intro N. apply Cls_ext. intros n Hn. apply in_seq in Hn.
  apply efac_conv. lia.
Qed.

End Principal.

Print Assumptions L0_eq_zeta_factor.

(* ================================================================= *)
(*  END CLPrincipal.v                                                 *)
(* ================================================================= *)

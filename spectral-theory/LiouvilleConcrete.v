(* ================================================================= *)
(*  LiouvilleConcrete.v  —  the ACTUAL Liouville function lambda, and   *)
(*  its prime-2 dyadic self-reference, tied to LiouvilleSign.          *)
(*                                                                    *)
(*  lambda(n) = (-1)^Omega(n) built by smallest-prime-factor recursion  *)
(*  (spf, from VonMangoldtGlobal): lambda(1)=1, lambda(n)=-lambda(n/spf n). *)
(*  We prove lambda is a genuine COMPLETELY-multiplicative sign:         *)
(*    lam_1, lam_sign, lam_2, and                                       *)
(*    lam_mult : lambda(m*n) = lambda(m)*lambda(n)  for ALL m,n         *)
(*      (= Omega-additivity), via lam_prime_step : lambda(p*n)=-lambda(n)  *)
(*      for p prime (peel one prime), then peel primes off m.           *)
(*  Hence lambda INSTANTIATES LiouvilleSign's abstract sign character:   *)
(*    tosym_lam_hom, val_tosym_lam : lambda = val o tosym_lam, a hom     *)
(*    into the {I,N} = Z/2 sign group -- the {I,N,F} thread is now the   *)
(*    real Liouville sign.  And the prime-2 special case lam_2m gives    *)
(*    the concrete dyadic identity                                       *)
(*    L_split_lam : L(x) = L_odd(x) - L(x/2)                            *)
(*  for the real L(x) = sum_{n<=x} lambda(n).  PNT = the mean of lambda   *)
(*  going to 0 (liouville_pnt_lam) -- the remaining parity boundary.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List ZArith Wf_nat.
Require Import RealMobius VonMangoldtGlobal LiouvilleSign INFMonoid.
Import ListNotations.

(* ---- lambda by smallest-prime-factor recursion (fuel = n) ---- *)
Fixpoint lam_f (fuel n : nat) : Z :=
  match fuel with
  | O => 1%Z
  | S f => if Nat.leb n 1 then 1%Z else Z.opp (lam_f f (n / spf n))
  end.
Definition lam (n : nat) : Z := lam_f n n.

(* for n <= 1 the fuel is irrelevant: lambda = 1 *)
Lemma lam_f_small : forall f n, (n <= 1)%nat -> lam_f f n = 1%Z.
Proof.
  intros [|f] n Hn; cbn [lam_f]; [ reflexivity | ].
  destruct (Nat.leb n 1) eqn:E; [ reflexivity | apply Nat.leb_gt in E; lia ].
Qed.

(* lam_f is independent of the fuel once fuel >= n (well-founded on n) *)
Lemma lam_f_stable : forall n f1 f2,
  (n <= f1)%nat -> (n <= f2)%nat -> lam_f f1 n = lam_f f2 n.
Proof.
  intro n; induction n as [n IH] using (well_founded_induction lt_wf);
    intros f1 f2 H1 H2.
  destruct (Nat.le_gt_cases n 1) as [Hle | Hgt].
  - rewrite (lam_f_small f1 n Hle), (lam_f_small f2 n Hle); reflexivity.
  - destruct f1 as [|f1']; [ lia | ]; destruct f2 as [|f2']; [ lia | ].
    cbn [lam_f].
    assert (En : Nat.leb n 1 = false) by (apply Nat.leb_gt; lia).
    rewrite En.
    assert (Hlt : (n / spf n < n)%nat)
      by (apply Nat.div_lt; [ lia | pose proof (spf_ge2 n ltac:(lia)); lia ]).
    f_equal; apply (IH (n / spf n)%nat Hlt); lia.
Qed.

(* the defining recurrence of lambda *)
Lemma lam_unfold : forall n, (2 <= n)%nat -> lam n = Z.opp (lam (n / spf n)).
Proof.
  intros n Hn; unfold lam at 1.
  destruct n as [|n']; [ lia | ]; cbn [lam_f].
  destruct (Nat.leb (S n') 1) eqn:E; [ apply Nat.leb_le in E; lia | ].
  f_equal; unfold lam.
  assert (Hlt : (S n' / spf (S n') < S n')%nat)
    by (apply Nat.div_lt; [ lia | pose proof (spf_ge2 (S n') ltac:(lia)); lia ]).
  apply lam_f_stable; lia.
Qed.

Lemma lam_1 : lam 1 = 1%Z.
Proof. reflexivity. Qed.

(* the smallest prime factor of an even number is 2 *)
Lemma spf_2m : forall m, (1 <= m)%nat -> spf (2 * m) = 2%nat.
Proof.
  intros m Hm.
  assert (H2 : (2 <= 2 * m)%nat) by lia.
  pose proof (spf_ge2 (2 * m) H2) as Hge.
  destruct (Nat.le_gt_cases (spf (2 * m)) 2) as [Hle | Hgt]; [ lia | exfalso ].
  apply (spf_least (2 * m) 2 H2); [ lia | exact Hgt | ].
  exists m; lia.
Qed.

(* THE structural fact: the Liouville sign flips at the prime 2 *)
Theorem lam_2m : forall m, (1 <= m)%nat -> lam (2 * m) = Z.opp (lam m).
Proof.
  intros m Hm; rewrite (lam_unfold (2 * m) ltac:(lia)), (spf_2m m Hm).
  replace (2 * m / 2)%nat with m by (rewrite Nat.mul_comm, Nat.div_mul; lia).
  reflexivity.
Qed.

Corollary lam_2 : lam 2 = (-1)%Z.
Proof. rewrite <- (Nat.mul_1_r 2), (lam_2m 1 ltac:(lia)), lam_1; reflexivity. Qed.

(* lambda is a genuine sign: lambda(n) in {+1,-1} for n >= 1 *)
Lemma lam_sign : forall n, (1 <= n)%nat -> lam n = 1%Z \/ lam n = (-1)%Z.
Proof.
  intro n; induction n as [n IH] using (well_founded_induction lt_wf); intro Hn.
  destruct (Nat.le_gt_cases n 1) as [Hle | Hgt].
  - assert (n = 1)%nat by lia; subst; left; exact lam_1.
  - rewrite (lam_unfold n ltac:(lia)).
    assert (Hlt : (n / spf n < n)%nat)
      by (apply Nat.div_lt; [ lia | pose proof (spf_ge2 n ltac:(lia)); lia ]).
    assert (Hge1 : (1 <= n / spf n)%nat).
    { pose proof (spf_ge2 n ltac:(lia)) as Hs2.
      pose proof (Nat.divide_pos_le (spf n) n ltac:(lia) (spf_divides n ltac:(lia))) as Hsle.
      destruct (Nat.eq_dec (n / spf n) 0) as [E | E]; [ exfalso | lia ].
      pose proof (Nat.div_mod_eq n (spf n)) as Hdm; rewrite E in Hdm.
      pose proof (Nat.mod_upper_bound n (spf n) ltac:(lia)); lia. }
    destruct (IH (n / spf n)%nat Hlt Hge1) as [H | H]; rewrite H; [ right | left ]; reflexivity.
Qed.

(* ================================================================= *)
(*  COMPLETE MULTIPLICATIVITY  lambda(mn) = lambda(m) lambda(n)         *)
(*  = Omega-additivity.  The crux is lambda(p*n) = -lambda(n) for p     *)
(*  prime (peel one prime), then peel primes off m.                    *)
(* ================================================================= *)
Open Scope nat_scope.

Lemma nprime_ge2 : forall p, nprime p -> 2 <= p.
Proof. intros p [H _]; exact H. Qed.

Lemma prime_div_eq : forall p q, nprime p -> Nat.divide q p -> 2 <= q -> q = p.
Proof. intros p q [_ Hpd] Hd Hq; destruct (Hpd q Hd) as [E | E]; [ lia | exact E ]. Qed.

(* peel one prime: lambda(p*n) = -lambda(n) *)
Lemma lam_prime_step : forall p, nprime p ->
  forall n, 1 <= n -> lam (p * n) = Z.opp (lam n).
Proof.
  intros p Hp; induction n as [n IH] using (well_founded_induction lt_wf); intro Hn.
  pose proof (nprime_ge2 p Hp) as Hp2.
  assert (Hpn2 : 2 <= p * n) by nia.
  rewrite (lam_unfold (p * n) Hpn2).
  remember (spf (p * n)) as q eqn:Hqdef.
  assert (Hqdvd : Nat.divide q (p * n)) by (rewrite Hqdef; apply spf_divides; exact Hpn2).
  assert (Hqp : nprime q) by (rewrite Hqdef; apply spf_nprime; exact Hpn2).
  pose proof (nprime_ge2 q Hqp) as Hq2.
  assert (Hqle : q <= p).
  { destruct (Nat.le_gt_cases q p) as [H | H]; [ exact H | exfalso ].
    rewrite Hqdef in H; apply (spf_least (p * n) p Hpn2 Hp2 H); exists n; ring. }
  destruct (Nat.eq_dec q p) as [Eq | Neq].
  - assert (Hpnq : p * n / q = n) by (rewrite Eq, Nat.mul_comm; apply Nat.div_mul; lia).
    rewrite Hpnq; reflexivity.
  - assert (Hqltp : q < p) by lia.
    assert (Hqn : Nat.divide q n).
    { destruct (nprime_euclid q p n Hqp Hqdvd) as [Hqp' | Hqn']; [ exfalso | exact Hqn' ].
      pose proof (prime_div_eq p q Hp Hqp' Hq2); lia. }
    destruct Hqn as [k Hk].
    assert (Hk1 : 1 <= k) by (destruct k; [ simpl in Hk; lia | lia ]).
    assert (Hn2 : 2 <= n) by nia.
    assert (Hnq : n / q = k) by (rewrite Hk; apply Nat.div_mul; lia).
    assert (Hdiv : p * n / q = p * k)
      by (rewrite Hk; replace (p * (k * q)) with (p * k * q) by ring;
          apply Nat.div_mul; lia).
    rewrite Hdiv.
    assert (Hklt : k < n) by nia.
    rewrite (IH k Hklt Hk1), (lam_unfold n Hn2).
    assert (Hspf : spf n = q).
    { assert (Hd1 : Nat.divide (spf n) (p * n))
        by (apply Nat.divide_trans with n; [ apply spf_divides; exact Hn2 | exists p; ring ]).
      assert (Hs2 : 2 <= spf n) by (apply spf_ge2; exact Hn2).
      destruct (Nat.lt_trichotomy (spf n) q) as [Hlt | [Heq | Hgt]].
      - exfalso; rewrite Hqdef in Hlt;
          apply (spf_least (p * n) (spf n) Hpn2 Hs2 Hlt); exact Hd1.
      - exact Heq.
      - exfalso; apply (spf_least n q Hn2 Hq2 Hgt); exists k; exact Hk. }
    rewrite Hspf, Hnq; ring.
Qed.

(* peel primes off m: complete multiplicativity *)
Theorem lam_mult : forall m n, 1 <= m -> 1 <= n -> lam (m * n) = (lam m * lam n)%Z.
Proof.
  intro m; induction m as [m IH] using (well_founded_induction lt_wf); intros n Hm Hn.
  destruct (Nat.le_gt_cases m 1) as [Hle | Hgt].
  - assert (m = 1) by lia; subst m; rewrite Nat.mul_1_l, lam_1; ring.
  - assert (Hm2 : 2 <= m) by lia.
    pose proof (spf_nprime m Hm2) as Hsp.
    pose proof (nprime_ge2 (spf m) Hsp) as Hsp2.
    pose proof (spf_divides m Hm2) as [j Hj].
    assert (Hj1 : 1 <= j) by (destruct j; [ simpl in Hj; lia | lia ]).
    assert (Hjlt : j < m) by nia.
    assert (Hlm : lam m = Z.opp (lam j))
      by (replace m with (spf m * j) by nia; apply (lam_prime_step (spf m) Hsp j Hj1)).
    replace (m * n) with (spf m * (j * n)) by nia.
    rewrite (lam_prime_step (spf m) Hsp (j * n) ltac:(nia)),
            (IH j Hjlt n Hj1 Hn), Hlm; ring.
Qed.

(* ================================================================= *)
(*  lambda NOW INSTANTIATES LiouvilleSign's abstract sign character:   *)
(*  lambda = val o tosym_lam, a hom into the {I,N} = Z/2 sign group.    *)
(* ================================================================= *)
Definition tosym_lam : nat -> Sym := tosym lam.

Theorem tosym_lam_hom : forall m n, 1 <= m -> 1 <= n ->
  tosym_lam (m * n) = op (tosym_lam m) (tosym_lam n).
Proof. exact (tosym_hom lam lam_mult lam_sign). Qed.

Theorem val_tosym_lam : forall n, 1 <= n -> val (tosym_lam n) = lam n.
Proof. exact (val_tosym lam lam_sign). Qed.

(* ================================================================= *)
(*  THE CONCRETE PRIME-2 DYADIC IDENTITY for the real Liouville sum.   *)
(* ================================================================= *)
Open Scope R_scope.

Definition Llam (x : nat) : R := Rls (seq 1 x) (fun n => IZR (lam n)).
Definition Llam_odd (x : nat) : R :=
  Rls (seq 1 x) (fun n => if negb (Nat.even n) then IZR (lam n) else 0).

(* the even part of L over [1,x] is  -L(x/2)  (via lambda(2m) = -lambda(m)) *)
Theorem L_even_lam : forall x,
  Rls (seq 1 x) (fun n => if Nat.even n then IZR (lam n) else 0) = - Llam (x / 2).
Proof.
  intros x; rewrite Rls_filter_ind, even_filter, Rls_map.
  unfold Llam; rewrite <- Rls_opp; apply Rls_ext; intros m Hm; apply in_seq in Hm.
  rewrite (lam_2m m ltac:(lia)), opp_IZR; reflexivity.
Qed.

(* the dyadic self-reference for the ACTUAL Liouville function *)
Theorem L_split_lam : forall x, Llam x = Llam_odd x - Llam (x / 2).
Proof.
  intros x; unfold Llam, Llam_odd.
  rewrite (Rls_ext _ (fun n => IZR (lam n))
             (fun n => (if negb (Nat.even n) then IZR (lam n) else 0)
                       + (if Nat.even n then IZR (lam n) else 0))).
  - rewrite Rls_add.
    pose proof (L_even_lam x) as He; unfold Llam in He; rewrite He; ring.
  - intros n _; destruct (Nat.even n); simpl; ring.
Qed.

(* ---- PNT, stated as the Liouville mean: the parity boundary ----
   PNT (psi ~ x, i.e. our alpha = 0 in SelbergPin, or PsiAsymp's Un_cv
   Vrem 0) is classically EQUIVALENT to this mean vanishing (both <->
   zeta(1+it) <> 0).  What this file delivers is the FULL algebraic
   STRUCTURE:
     - lambda satisfies ALL FOUR hypotheses of Section Sign: lam_1,
       lam_mult (complete multiplicativity = Omega-additivity), lam_sign,
       lam_2 -- so lambda = val o tosym_lam factors through the {I,N}
       sign group (tosym_lam_hom, val_tosym_lam);
     - the prime-2 self-reference lam_2m + L_split_lam.
   What it does NOT deliver -- the genuine remaining gap:
     - the CANCELLATION liouville_pnt_lam itself: Sum lambda(n) = o(x),
       proven nowhere (PsiAsymp.pnt_of_avg_below is only conditional on
       avg_below).  This is the parity problem = alpha = 0.  The sign
       STRUCTURE is entirely here; the mean-zero CANCELLATION is not. *)
Definition liouville_pnt_lam : Prop := Un_cv (fun x => Llam x / INR x) 0.

Print Assumptions lam_mult.
Print Assumptions tosym_lam_hom.
Print Assumptions L_split_lam.

(* ================================================================= *)
(*  END LiouvilleConcrete.v  —  the real Liouville lambda, lambda(2m) =  *)
(*  -lambda(m), and L(x) = L_odd(x) - L(x/2).  PNT = mean of lambda -> 0. *)
(* ================================================================= *)

(* ================================================================= *)
(*  MuLog.v  —  the divisor double-sum swap and  Lam = mu * log.        *)
(*                                                                    *)
(*  div_swap :  Sum_{d|n} Sum_{e|(n/d)} F d e = Sum_{e|n} Sum_{d|(n/e)} *)
(*              F d e   (real Fubini over the divisor lattice),         *)
(*  proved by a Permutation of the two pair-enumerations of            *)
(*  { (d,e) : d*e | n }.  Then Mobius inversion of                      *)
(*  Sum_{d|n} Lam(d) = ln n (vonmangoldt_identity) gives                *)
(*      Lam n = Sum_{d|n} mu(d) ln(n/d).                                *)
(*  Selberg route, Step 2b.  Axiom-clean.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Permutation.
Require Import DirichletConv VonMangoldtGlobal RealMobius.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  A.  list infrastructure                                           *)
(* ================================================================= *)

Lemma Rls_map : forall A B (g : A -> B) (f : B -> R) l,
  Rls (map g l) f = Rls l (fun x => f (g x)).
Proof.
  intros A B g f l; induction l as [|a l IH]; [ reflexivity | ].
  cbn [map]; rewrite !Rls_cons, IH; reflexivity.
Qed.

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd; induction Hnd as [| x l Hx Hnd IH]; cbn [map]; constructor.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Hfy Hy]].
    assert (x = y) by (apply Hinj; [ left; reflexivity | right; exact Hy | symmetry; exact Hfy ]).
    subst y; contradiction.
  - apply IH; intros a b Ha Hb Hab; apply Hinj; [ right; exact Ha | right; exact Hb | exact Hab ].
Qed.

Lemma NoDup_app : forall A (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hd; induction l1 as [|a l1 IH]; [ exact H2 | ].
  inversion H1 as [|? ? Hna Hnd]; subst; cbn [app]; constructor.
  - intro Hin; apply in_app_or in Hin; destruct Hin as [Hin | Hin];
      [ contradiction | apply (Hd a (in_eq a l1) Hin) ].
  - apply IH; [ exact Hnd | intros x Hx; apply Hd; right; exact Hx ].
Qed.

(* pair enumeration of a nested divisor sum *)
Definition flatpair (g : nat -> list nat) (l : list nat) : list (nat * nat) :=
  flat_map (fun d => map (fun e => (d, e)) (g d)) l.

Lemma in_flatpair : forall g l d e,
  In (d, e) (flatpair g l) <-> (In d l /\ In e (g d)).
Proof.
  intros g l d e; unfold flatpair; rewrite in_flat_map; split.
  - intros [d0 [Hd0 Hin]]; apply in_map_iff in Hin; destruct Hin as [e0 [Heq He0]].
    injection Heq as -> ->; split; assumption.
  - intros [Hd He]; exists d; split;
      [ exact Hd | apply in_map_iff; exists e; split; [ reflexivity | exact He ] ].
Qed.

Lemma NoDup_flatpair : forall g l,
  NoDup l -> (forall d, NoDup (g d)) -> NoDup (flatpair g l).
Proof.
  intros g l; induction l as [|a l IH]; intros Hnd Hg; [ constructor | ].
  inversion Hnd as [|? ? Hna Hnl]; subst; cbn [flatpair flat_map]; apply NoDup_app.
  - apply NoDup_map_inj; [ intros x y _ _ Heq; congruence | apply Hg ].
  - apply IH; [ exact Hnl | exact Hg ].
  - intros x Hin1 Hin2; apply in_map_iff in Hin1; destruct Hin1 as [e0 [Heq _]].
    change (flat_map (fun d => map (fun e => (d, e)) (g d)) l) with (flatpair g l) in Hin2.
    destruct x as [xd xe]; rewrite in_flatpair in Hin2; destruct Hin2 as [Hxd _].
    assert (xd = a) by congruence; subst xd; contradiction.
Qed.

Lemma Rls_flatpair : forall (F : nat -> nat -> R) g l,
  Rls (flatpair g l) (fun de => F (fst de) (snd de))
  = Rls l (fun d => Rls (g d) (fun e => F d e)).
Proof.
  intros F g l; unfold flatpair; rewrite Rls_flat_map.
  apply Rls_ext; intros d _; rewrite Rls_map; reflexivity.
Qed.

(* ================================================================= *)
(*  B.  the pair set  { (d,e) : d*e | n }  is symmetric               *)
(* ================================================================= *)

Lemma pair_div : forall n d e, (1 <= n)%nat ->
  (In d (divisors n) /\ In e (divisors (n / d)))
  <-> (Nat.divide (d * e) n /\ 1 <= d /\ 1 <= e)%nat.
Proof.
  intros n d e Hn; split.
  - intros [Hd He].
    apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] Hddiv].
    apply in_divisors in He; destruct He as [[He1 Hen] Hediv].
    destruct Hddiv as [k Hk]; destruct Hediv as [j Hj].
    (* n = k*d, n/d = k, k = j*e *)
    assert (Hnd : (n / d = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
    rewrite Hnd in Hj.
    split; [ exists j; rewrite Hk, Hj; ring | lia ].
  - intros [Hdiv [Hd1 He1]].
    destruct Hdiv as [q Hq].  (* n = q * (d*e) *)
    assert (Hdn : Nat.divide d n) by (exists (q * e)%nat; rewrite Hq; ring).
    assert (Hnd : (n / d = q * e)%nat).
    { rewrite Hq; replace (q * (d * e))%nat with ((q * e) * d)%nat by ring;
        rewrite Nat.div_mul by lia; reflexivity. }
    split; apply in_divisors.
    + split; [ split; [ exact Hd1 | apply Nat.divide_pos_le; [ lia | exact Hdn ] ] | exact Hdn ].
    + rewrite Hnd; split.
      * split; [ exact He1 | ].
        apply Nat.divide_pos_le; [ nia | exists q; ring ].
      * exists q; ring.
Qed.

Lemma pair_swap_iff : forall n d e, (1 <= n)%nat ->
  (In d (divisors n) /\ In e (divisors (n / d)))
  <-> (In e (divisors n) /\ In d (divisors (n / e))).
Proof.
  intros n d e Hn; rewrite !(pair_div n) by exact Hn.
  split; intros [Hdiv [H1 H2]]; (split; [ | split ]);
    try assumption; try (rewrite Nat.mul_comm; exact Hdiv).
Qed.

(* pair enumeration grouped by the SECOND index *)
Definition flatpair2 (g : nat -> list nat) (l : list nat) : list (nat * nat) :=
  flat_map (fun e => map (fun d => (d, e)) (g e)) l.

Lemma in_flatpair2 : forall g l d e,
  In (d, e) (flatpair2 g l) <-> (In e l /\ In d (g e)).
Proof.
  intros g l d e; unfold flatpair2; rewrite in_flat_map; split.
  - intros [e0 [He0 Hin]]; apply in_map_iff in Hin; destruct Hin as [d0 [Heq Hd0]].
    injection Heq as -> ->; split; assumption.
  - intros [He Hd]; exists e; split;
      [ exact He | apply in_map_iff; exists d; split; [ reflexivity | exact Hd ] ].
Qed.

Lemma NoDup_flatpair2 : forall g l,
  NoDup l -> (forall e, NoDup (g e)) -> NoDup (flatpair2 g l).
Proof.
  intros g l; induction l as [|a l IH]; intros Hnd Hg; [ constructor | ].
  inversion Hnd as [|? ? Hna Hnl]; subst; cbn [flatpair2 flat_map]; apply NoDup_app.
  - apply NoDup_map_inj; [ intros x y _ _ Heq; congruence | apply Hg ].
  - apply IH; [ exact Hnl | exact Hg ].
  - intros x Hin1 Hin2; apply in_map_iff in Hin1; destruct Hin1 as [d0 [Heq _]].
    change (flat_map (fun e => map (fun d => (d, e)) (g e)) l) with (flatpair2 g l) in Hin2.
    destruct x as [xd xe]; rewrite in_flatpair2 in Hin2; destruct Hin2 as [Hxe _].
    assert (xe = a) by congruence; subst xe; contradiction.
Qed.

Lemma Rls_flatpair2 : forall (F : nat -> nat -> R) g l,
  Rls (flatpair2 g l) (fun de => F (fst de) (snd de))
  = Rls l (fun e => Rls (g e) (fun d => F d e)).
Proof.
  intros F g l; unfold flatpair2; rewrite Rls_flat_map.
  apply Rls_ext; intros e _; rewrite Rls_map; reflexivity.
Qed.

(* ================================================================= *)
(*  C.  the divisor double-sum swap                                   *)
(* ================================================================= *)

Theorem div_swap : forall (F : nat -> nat -> R) n, (1 <= n)%nat ->
  Rls (divisors n) (fun d => Rls (divisors (n / d)) (fun e => F d e))
  = Rls (divisors n) (fun e => Rls (divisors (n / e)) (fun d => F d e)).
Proof.
  intros F n Hn.
  rewrite <- (Rls_flatpair F (fun d => divisors (n / d)) (divisors n)).
  rewrite <- (Rls_flatpair2 F (fun e => divisors (n / e)) (divisors n)).
  apply Rls_perm, NoDup_Permutation.
  - apply NoDup_flatpair; [ apply divisors_nodup | intro; apply divisors_nodup ].
  - apply NoDup_flatpair2; [ apply divisors_nodup | intro; apply divisors_nodup ].
  - intros [d e]; rewrite in_flatpair, in_flatpair2; apply pair_swap_iff; exact Hn.
Qed.

Print Assumptions div_swap.

(* ================================================================= *)
(*  D.  Lam = mu * log                                                *)
(* ================================================================= *)

Lemma Rls_zero : forall A (l : list A), Rls l (fun _ => 0) = 0.
Proof.
  intros A l; induction l as [|a l IH]; [ reflexivity | rewrite Rls_cons, IH; ring ].
Qed.

Lemma Rls_sift0 : forall (l : list nat) (c : R) m, NoDup l -> In m l ->
  Rls l (fun x => if Nat.eqb x m then c else 0) = c.
Proof.
  intros l c m; induction l as [|a l IH]; intros Hnd Hin; [ destruct Hin | ].
  inversion Hnd as [|? ? Hna Hnl]; subst; rewrite Rls_cons; cbn beta.
  destruct (Nat.eqb_spec a m) as [->|Hne].
  - change (if true then c else 0) with c.
    rewrite (Rls_ext _ (fun x => if Nat.eqb x m then c else 0) (fun _ => 0) l), Rls_zero.
    + ring.
    + intros x Hx; destruct (Nat.eqb_spec x m) as [->|]; [ contradiction | reflexivity ].
  - change (if false then c else 0) with 0.
    destruct Hin as [->|Hin]; [ contradiction | ].
    rewrite (IH Hnl Hin); ring.
Qed.

Lemma Rls_sift : forall (l : list nat) (h : nat -> R) m, NoDup l -> In m l ->
  Rls l (fun x => if Nat.eqb x m then h x else 0) = h m.
Proof.
  intros l h m Hnd Hin.
  rewrite (Rls_ext _ (fun x => if Nat.eqb x m then h x else 0)
                     (fun x => if Nat.eqb x m then h m else 0) l)
    by (intros x _; destruct (Nat.eqb_spec x m) as [->|]; reflexivity).
  apply Rls_sift0; assumption.
Qed.

Theorem Lam_eq_mulog : forall n, (1 <= n)%nat ->
  Lam n = Rls (divisors n) (fun d => IZR (mu d) * ln (INR (n / d))).
Proof.
  intros n Hn; symmetry.
  (* expand ln(n/d) = Sum_{e|(n/d)} Lam e and pull mu(d) in *)
  transitivity (Rls (divisors n)
                  (fun d => Rls (divisors (n / d)) (fun e => IZR (mu d) * Lam e))).
  { apply Rls_ext; intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] Hdd].
    assert (Hndd : (1 <= n / d)%nat)
      by (destruct Hdd as [k Hk]; rewrite Hk, Nat.div_mul by lia; nia).
    change (fold_right Rplus 0 (map Lam (divisors (n / d)))) with (dsum Lam (n / d)).
    rewrite <- (vonmangoldt_identity (n / d) Hndd).
    unfold dsum; rewrite <- (Rls_scal _ (IZR (mu d)) Lam); reflexivity. }
  (* swap the order of summation *)
  rewrite (div_swap (fun d e => IZR (mu d) * Lam e) n Hn).
  (* inner: Sum_{d|(n/e)} mu(d) Lam(e) = Lam(e) * [n/e = 1] *)
  transitivity (Rls (divisors n) (fun e => if Nat.eqb (n / e) 1 then Lam e else 0)).
  { apply Rls_ext; intros e He; apply in_divisors in He; destruct He as [[He1 Hen] Hed].
    assert (Hnde : (1 <= n / e)%nat)
      by (destruct Hed as [k Hk]; rewrite Hk, Nat.div_mul by lia; nia).
    rewrite (Rls_ext _ _ (fun d => Lam e * IZR (mu d))) by (intros; ring).
    rewrite <- Rls_scal, mu_real_sum by exact Hnde.
    destruct (Nat.eqb (n / e) 1); ring. }
  (* only e = n survives (n/e = 1 <-> e = n on divisors of n) *)
  rewrite (Rls_ext _ _ (fun e => if Nat.eqb e n then Lam e else 0)).
  - apply Rls_sift; [ apply divisors_nodup | apply in_divisors; repeat split;
      [ lia | lia | exists 1%nat; ring ] ].
  - intros e He; apply in_divisors in He; destruct He as [[He1 Hen] Hed].
    destruct Hed as [k Hk].
    assert (n / e = k)%nat by (rewrite Hk, Nat.div_mul; lia).
    destruct (Nat.eqb_spec (n / e) 1) as [E1|E1]; destruct (Nat.eqb_spec e n) as [E2|E2];
      try reflexivity; subst; try (exfalso; nia).
Qed.

Print Assumptions Lam_eq_mulog.

(* ================================================================= *)
(*  END MuLog.v                                                       *)
(*  Lam n = Sum_{d|n} mu(d) ln(n/d) — the Selberg-route Mobius bridge. *)
(* ================================================================= *)

(* ================================================================= *)
(*  CichonPoset.v  —  THE CICHOŃ DIAGRAM AS A FINITE POSET.           *)
(*                                                                    *)
(*  The Cichoń diagram of cardinal characteristics of the continuum,  *)
(*  as a finite partial order (the ZFC-provable ≤ arrows).  Nodes:    *)
(*                                                                    *)
(*    ℵ₁ ─→ add(𝒩) ─→ add(ℳ) ─→ cov(ℳ) ─→ non(𝒩) ─→ cof(𝒩) ─→ 𝔠     *)
(*             │          │  ╲       │  ╲       ↑          ↑          *)
(*             ↓          ↓   ↘      ↓   ↘      │          │          *)
(*          cov(𝒩) ───────────→ 𝔟 ─→ 𝔡 ─→ cof(ℳ) ─────────┘          *)
(*                              (add(ℳ)→𝔟, cov(ℳ)→𝔡, cov(𝒩)→non(ℳ)) *)
(*                                                                    *)
(*  We give the 15 covering arrows, take cle = their reflexive-       *)
(*  transitive closure, and prove (cle) is a genuine PARTIAL ORDER    *)
(*  (reflexive, transitive, ANTISYMMETRIC) — the antisymmetry via a   *)
(*  rank (a linear extension: every arrow strictly increases rank).   *)
(*  It is genuinely partial, not a chain: cov(𝒩) ⊥ add(ℳ), certified  *)
(*  by an UP-SET (= an Alexandrov open, `PosetTopology.Op`) that       *)
(*  separates them.                                                   *)
(*                                                                    *)
(*  Repo ties: the BOTTOM ℵ₁ and TOP 𝔠 = 2^ℵ₀ = |ℤ₂| are the two      *)
(*  endpoints proved elsewhere (`PadicUncountable.Zp2_uncountable`    *)
(*  for 𝔠 > ℵ₀), and the interior arrow 𝔟 ≤ 𝔡 (`b_le_d`) is the       *)
(*  diagram edge whose `> ℵ₀` lower bound is `DominatingModulus`.     *)
(*  AXIOM-FREE (Closed under the global context).                    *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia.

(* the twelve cardinal characteristics (bnum=𝔟, dnum=𝔡, cont=𝔠) *)
Inductive Node : Type :=
  aleph1 | addN | addM | covN | covM | nonN | nonM | bnum | dnum | cofM | cofN | cont.

(* the 15 covering arrows  a → b  (meaning a ≤ b, ZFC-provable) *)
Inductive arrow : Node -> Node -> Prop :=
| ar_al_addN  : arrow aleph1 addN
| ar_addN_addM: arrow addN   addM
| ar_addN_covN: arrow addN   covN
| ar_addM_covM: arrow addM   covM
| ar_addM_b   : arrow addM   bnum
| ar_b_d      : arrow bnum   dnum
| ar_b_nonM   : arrow bnum   nonM
| ar_covN_nonM: arrow covN   nonM
| ar_covM_d   : arrow covM   dnum
| ar_covM_nonN: arrow covM   nonN
| ar_d_cofM   : arrow dnum   cofM
| ar_nonM_cofM: arrow nonM   cofM
| ar_nonN_cofN: arrow nonN   cofN
| ar_cofM_cofN: arrow cofM   cofN
| ar_cofN_c   : arrow cofN   cont.

(* the order: reflexive-transitive closure (an arrow-path) *)
Inductive cle : Node -> Node -> Prop :=
| cle_refl : forall x, cle x x
| cle_step : forall x y z, arrow x y -> cle y z -> cle x z.

Local Hint Constructors cle arrow : cichon.

Lemma cle_trans : forall x y z, cle x y -> cle y z -> cle x z.
Proof.
  intros x y z Hxy; revert z; induction Hxy as [x | x y w Ha Hyw IH]; intros z Hz.
  - exact Hz.
  - apply (cle_step x y z Ha), IH, Hz.
Qed.

(* ----------------------------------------------------------------- *)
(*  ANTISYMMETRY via a rank (a linear extension of the diagram)       *)
(* ----------------------------------------------------------------- *)
Definition rank (x : Node) : nat :=
  match x with
  | aleph1 => 0 | addN => 1 | covN => 2 | addM => 3 | bnum => 4 | covM => 5
  | dnum => 6 | nonM => 7 | nonN => 8 | cofM => 9 | cofN => 10 | cont => 11
  end.

Lemma rank_inj : forall x y, rank x = rank y -> x = y.
Proof. intros x y; destruct x; destruct y; intro H; try reflexivity; discriminate H. Qed.

Lemma arrow_rank_lt : forall x y, arrow x y -> (rank x < rank y)%nat.
Proof. intros x y H; destruct H; cbn [rank]; lia. Qed.

Lemma cle_rank_le : forall x y, cle x y -> (rank x <= rank y)%nat.
Proof.
  intros x y H; induction H as [x | x y z Ha Hyz IH].
  - apply Nat.le_refl.
  - pose proof (arrow_rank_lt x y Ha); lia.
Qed.

Theorem cle_antisym : forall x y, cle x y -> cle y x -> x = y.
Proof.
  intros x y Hxy Hyx; apply rank_inj.
  pose proof (cle_rank_le x y Hxy); pose proof (cle_rank_le y x Hyx); lia.
Qed.

(* ================================================================= *)
(*  THE MASTER THEOREM: (Node, cle) is a finite POSET.               *)
(* ================================================================= *)
Theorem cichon_poset :
  (forall x, cle x x)
  /\ (forall x y z, cle x y -> cle y z -> cle x z)
  /\ (forall x y, cle x y -> cle y x -> x = y).
Proof. split; [ exact cle_refl | split; [ exact cle_trans | exact cle_antisym ] ]. Qed.

(* ----------------------------------------------------------------- *)
(*  Endpoints and the interior 𝔟 ≤ 𝔡, by path search.                 *)
(* ----------------------------------------------------------------- *)
Theorem bottom : forall x, cle aleph1 x.     (* ℵ₁ is the least element *)
Proof. destruct x; eauto 20 with cichon. Qed.

Theorem top : forall x, cle x cont.          (* 𝔠 = 2^ℵ₀ = |ℤ₂| is the greatest *)
Proof. destruct x; eauto 20 with cichon. Qed.

Theorem b_le_d : cle bnum dnum.              (* 𝔟 ≤ 𝔡  — the DominatingModulus edge *)
Proof. eauto with cichon. Qed.

(* ----------------------------------------------------------------- *)
(*  It is a genuine PARTIAL order, not a chain:  cov(𝒩) ⊥ add(ℳ).     *)
(*  Certificate: an UP-SET (an Alexandrov open, PosetTopology.Op)     *)
(*  containing one but not the other; cle propagates membership up.   *)
(* ----------------------------------------------------------------- *)
Definition up_closed (U : Node -> bool) : Prop :=
  forall x y, arrow x y -> U x = true -> U y = true.

Lemma cle_up : forall U, up_closed U ->
  forall x y, cle x y -> U x = true -> U y = true.
Proof.
  intros U HU x y H; induction H as [x | x y z Ha Hyz IH]; intro Hx.
  - exact Hx.
  - apply IH, (HU x y Ha Hx).
Qed.

(* the up-set of cov(𝒩), and the up-set of add(ℳ) *)
Definition upCovN (x : Node) : bool :=
  match x with covN | nonM | cofM | cofN | cont => true | _ => false end.
Definition upAddM (x : Node) : bool :=
  match x with addM | covM | bnum | dnum | nonM | nonN | cofM | cofN | cont => true
             | _ => false end.

Lemma upCovN_closed : up_closed upCovN.
Proof. intros x y H; destruct H; cbn [upCovN]; congruence. Qed.
Lemma upAddM_closed : up_closed upAddM.
Proof. intros x y H; destruct H; cbn [upAddM]; congruence. Qed.

Theorem covN_addM_incomparable : ~ cle covN addM /\ ~ cle addM covN.
Proof.
  split; intro H.
  - pose proof (cle_up upCovN upCovN_closed covN addM H eq_refl); discriminate.
  - pose proof (cle_up upAddM upAddM_closed addM covN H eq_refl); discriminate.
Qed.

Print Assumptions cichon_poset.

(* ================================================================= *)
(*  END CichonPoset.v                                                *)
(*  The Cichoń diagram as an axiom-free finite poset (reflexive,      *)
(*  transitive, antisymmetric), with ℵ₁ the bottom and 𝔠 = |ℤ₂| the  *)
(*  top, 𝔟 ≤ 𝔡 interior, and cov(𝒩) ⊥ add(ℳ) separated by an          *)
(*  Alexandrov open.  Closed under the global context.               *)
(* ================================================================= *)

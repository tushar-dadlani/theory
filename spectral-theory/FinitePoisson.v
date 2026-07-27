(* ================================================================= *)
(*  FinitePoisson.v  —  FINITE POISSON SUMMATION over ℤ/N.           *)
(*                                                                    *)
(*  The discrete shadow of Poisson summation, on the DFT cluster.     *)
(*  For N = d·m and f : ℤ/N → ℂ, summing the DFT over the dual        *)
(*  subgroup {r·d} recovers the sum of f over the subgroup {a·m}:     *)
(*                                                                    *)
(*    finite_poisson :                                                *)
(*       Σ_{r<m} (DFT_N f)(r·d) = m · Σ_{a<d} f(a·m).                 *)
(*                                                                    *)
(*  Proof: swap the double sum (`Csum_swap`), pull f(k) out, and the  *)
(*  inner geometric sum Σ_{r<m} (wc_N^{dk})^r is m if m∣k and 0       *)
(*  otherwise (`orth_val`, via `sum_pow_eq_0/1` + `wc` primitivity —  *)
(*  itself from `w_primitive` and `wc·w=1`); then the subgroup        *)
(*  reindex k = a·m + b keeps only b=0 (`sum_multiples`, `Csum_delta`).*)
(*                                                                    *)
(*  Quarantined (via `ComplexField`, C = ℝ×ℝ, so `Print Assumptions`  *)
(*  shows the classical-ℝ axioms).  HONEST SCOPE: this is the FINITE  *)
(*  Poisson formula — the exact, elementary analogue.  It is NOT the  *)
(*  continuous Σ_n f(n) = Σ_k f̂(k) (which needs improper integrals + *)
(*  Fourier convergence) and does NOT advance the functional          *)
(*  equation.  It closes the discrete-Fourier arc (DFT/IDFT/Parseval) *)
(*  with its Poisson identity.                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField RootsOfUnity DFTInversion.
Local Open Scope nat_scope.

(* ---- Csum toolkit ---- *)
Lemma Csum_add : forall f g N, Csum (fun k => Cadd (f k) (g k)) N = Cadd (Csum f N) (Csum g N).
Proof. intros f g N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite IH; ring ]. Qed.
Lemma Csum_mul_l : forall c f N, Csum (fun k => Cmul c (f k)) N = Cmul c (Csum f N).
Proof. intros c f N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite IH; ring ]. Qed.
Lemma Csum_zero : forall N, Csum (fun _ => C0) N = C0.
Proof. induction N as [|N IH]; cbn [Csum]; [ ring | rewrite IH; ring ]. Qed.
Lemma Csum_decomp : forall f N, Csum f (S N) = Cadd (f O) (Csum (fun i => f (S i)) N).
Proof.
  intros f N; induction N as [|N IH].
  - cbn [Csum]; ring.
  - change (Csum f (S (S N))) with (Cadd (Csum f (S N)) (f (S N))); rewrite IH.
    change (Csum (fun i => f (S i)) (S N)) with (Cadd (Csum (fun i => f (S i)) N) (f (S N))); ring.
Qed.
Lemma Csum_ext_lt : forall f g N, (forall k, (k < N)%nat -> f k = g k) -> Csum f N = Csum g N.
Proof. intros f g N; induction N as [|N IH]; intro H; cbn [Csum]; [ reflexivity | ].
  rewrite IH by (intros k Hk; apply H; lia); rewrite (H N) by lia; reflexivity. Qed.
Lemma Csum_swap : forall (g : nat -> nat -> C) M P,
  Csum (fun a => Csum (fun j => g a j) P) M = Csum (fun j => Csum (fun a => g a j) M) P.
Proof.
  intros g M P; induction M as [|M IH]; cbn [Csum].
  - rewrite Csum_zero; reflexivity.
  - rewrite IH, <- Csum_add. apply Csum_ext; intro j; cbn [Csum]; reflexivity.
Qed.
Lemma Csum_split : forall f a b, Csum f (a + b) = Cadd (Csum f a) (Csum (fun i => f (a + i)) b).
Proof.
  intros f a b; induction b as [|b IH].
  - replace (a + 0)%nat with a by lia; cbn [Csum]; ring.
  - replace (a + S b)%nat with (S (a + b)) by lia.
    change (Csum f (S (a + b))) with (Cadd (Csum f (a + b)) (f (a + b))); rewrite IH.
    change (Csum (fun i => f (a + i)) (S b)) with (Cadd (Csum (fun i => f (a + i)) b) (f (a + b))); ring.
Qed.

(* ---- wc primitivity ---- *)
Lemma Cpow_Cmul : forall a b n, Cpow (Cmul a b) n = Cmul (Cpow a n) (Cpow b n).
Proof. intros a b n; induction n as [|n IH]; cbn [Cpow]; [ ring | rewrite IH; ring ]. Qed.
Lemma wc_primitive : forall N j, (0 < j < N)%nat -> Cpow (wc N) j <> C1.
Proof.
  intros N j Hj Heq.
  assert (H : Cmul (Cpow (wc N) j) (Cpow (w N) j) = C1)
    by (rewrite <- Cpow_Cmul, wc_w_1, Cpow_C1; reflexivity).
  rewrite Heq in H. replace (Cmul C1 (Cpow (w N) j)) with (Cpow (w N) j) in H by ring.
  exact (w_primitive N j Hj H).
Qed.
Lemma wc_pow_period : forall N j, (0 < N)%nat -> Cpow (wc N) j = Cpow (wc N) (j mod N).
Proof.
  intros N j HN. rewrite (Nat.div_mod_eq j N) at 1.
  rewrite Cpow_add, Cpow_mul, wc_pow_N by exact HN. rewrite Cpow_C1.
  replace (Cmul C1 (Cpow (wc N) (j mod N))) with (Cpow (wc N) (j mod N)) by ring. reflexivity.
Qed.

(* ---- the inner geometric sum: m if m|k, else 0 ---- *)
Lemma orth_val : forall d m k, (0 < d)%nat -> (0 < m)%nat ->
  Csum (fun r => Cpow (wc (d * m)) (r * d * k)) m
  = (if (k mod m =? 0)%nat then RtoC (INR m) else C0).
Proof.
  intros d m k Hd Hm. set (N := (d * m)%nat). set (b := Cpow (wc N) (d * k)).
  assert (Hterm : forall r, Cpow (wc N) (r * d * k) = Cpow b r)
    by (intro r; unfold b; rewrite <- Cpow_mul; f_equal; lia).
  rewrite (Csum_ext _ (fun r => Cpow b r) m Hterm).
  assert (Hbm : Cpow b m = C1).
  { unfold b; rewrite <- Cpow_mul. replace (d * k * m)%nat with (N * k)%nat by (unfold N; nia).
    rewrite Cpow_mul, wc_pow_N by (unfold N; nia). apply Cpow_C1. }
  destruct (k mod m =? 0)%nat eqn:E.
  - apply Nat.eqb_eq in E.
    assert (Hb1 : b = C1).
    { unfold b. replace (d * k)%nat with (N * (k / m))%nat
        by (unfold N; pose proof (Nat.div_mod_eq k m); nia).
      rewrite Cpow_mul, wc_pow_N by (unfold N; nia). apply Cpow_C1. }
    rewrite (sum_pow_eq_1 b m Hb1); reflexivity.
  - apply Nat.eqb_neq in E.
    assert (Hbne : b <> C1).
    { unfold b. replace (d * k)%nat with (N * (k / m) + d * (k mod m))%nat
        by (unfold N; pose proof (Nat.div_mod_eq k m); nia).
      rewrite Cpow_add, Cpow_mul, wc_pow_N by (unfold N; nia). rewrite Cpow_C1.
      replace (Cmul C1 (Cpow (wc N) (d * (k mod m)))) with (Cpow (wc N) (d * (k mod m))) by ring.
      apply wc_primitive. unfold N.
      pose proof (Nat.mod_upper_bound k m ltac:(lia)). split; nia. }
    rewrite (sum_pow_eq_0 b m Hbne Hbm); reflexivity.
Qed.

Lemma Csum_delta : forall (h : nat -> C) (c : C) m, (0 < m)%nat ->
  Csum (fun i => Cmul (h i) (if (i =? 0)%nat then c else C0)) m = Cmul (h 0%nat) c.
Proof.
  intros h c m Hm. destruct m as [|m']; [ lia | ].
  rewrite Csum_decomp; cbn [Nat.eqb].
  rewrite (Csum_ext (fun i => Cmul (h (S i)) C0) (fun _ => C0)) by (intro; ring).
  rewrite Csum_zero; ring.
Qed.

Lemma sum_multiples : forall (g : nat -> C) d m, (0 < m)%nat ->
  Csum (fun k => Cmul (g k) (if (k mod m =? 0)%nat then RtoC (INR m) else C0)) (d * m)
  = Cmul (RtoC (INR m)) (Csum (fun a => g (a * m)) d).
Proof.
  intros g d m Hm; induction d as [|d IH].
  - replace (0 * m)%nat with 0%nat by lia; cbn [Csum]; ring.
  - replace (S d * m)%nat with (d * m + m)%nat by lia.
    rewrite Csum_split, IH.
    assert (Hblock : Csum (fun i => Cmul (g (d * m + i))
                (if ((d * m + i) mod m =? 0)%nat then RtoC (INR m) else C0)) m
              = Cmul (g (d * m)) (RtoC (INR m))).
    { rewrite (Csum_ext_lt _ (fun i => Cmul (g (d * m + i)) (if (i =? 0)%nat then RtoC (INR m) else C0)) m).
      2:{ intros i Hi. f_equal. replace ((d * m + i) mod m) with i;
          [ reflexivity | rewrite Nat.add_comm, Nat.mod_add by lia; symmetry; apply Nat.mod_small; lia ]. }
      rewrite (Csum_delta (fun i => g (d * m + i)) (RtoC (INR m)) m Hm).
      replace (d * m + 0)%nat with (d * m)%nat by lia; reflexivity. }
    rewrite Hblock; cbn [Csum]; ring.
Qed.

Theorem finite_poisson : forall d m (f : nat -> C), (0 < d)%nat -> (0 < m)%nat ->
  Csum (fun r => DFT (d * m) f (r * d)) m
  = Cmul (RtoC (INR m)) (Csum (fun a => f (a * m)) d).
Proof.
  intros d m f Hd Hm. unfold DFT.
  rewrite (Csum_swap (fun r k => Cmul (f k) (Cpow (wc (d * m)) (r * d * k))) m (d * m)).
  rewrite <- (sum_multiples f d m Hm).
  apply Csum_ext; intro k.
  rewrite (Csum_mul_l (f k) (fun r => Cpow (wc (d * m)) (r * d * k)) m).
  rewrite (orth_val d m k Hd Hm); reflexivity.
Qed.

Print Assumptions finite_poisson.

(* ================================================================= *)
(*  END FinitePoisson.v.  Σ_{r<m}(DFT_N f)(rd) = m·Σ_{a<d}f(am),      *)
(*  N=dm — the finite Poisson summation formula.                     *)
(* ================================================================= *)

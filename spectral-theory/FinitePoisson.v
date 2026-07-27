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

From Stdlib Require Import Reals Lra Lia Arith List Permutation QArith Qcanon.
Import ListNotations.
Require Import QPoly QPolyEmbed QPolyCoeffPIT QPolyQuot CycloOrthogonality DFTInversion DFTConvolution.
Require Import ComplexField RootsOfUnity.   (* last: ComplexField.C and DFTInversion.wc win *)
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

(* ================================================================================= *)
(*  THE AXIOM-FREE ALGEBRAIC FINITE POISSON SUMMATION, over R = ℚ[x]/(Φ_{dm}).        *)
(*  Σ_{r<m} DFT_R(dm) f (r·d) = m · Σ_{a<d} f(a·m), with ζ in place of the trans-      *)
(*  cendental root.  The orthogonality is a length-m geometric sum inside the         *)
(*  modulus-dm ring; its unit ζ^E−1 (for m∤k) comes from a generalized version of     *)
(*  zeta_pow_sub_unit via periodicity.  Print Assumptions = Closed under global ctx.  *)
(* ================================================================================= *)

Section RGeneric.
  Variable Nn : nat.
  Hypothesis HNg : (1 <= Nn)%nat.
  Local Open Scope Qc_scope.
  Notation Rq := (req Nn).

  Lemma req_sub_l : forall a a' c, Rq a a' -> Rq (qsub a c) (qsub a' c).
  Proof.
    intros a a' c [r Hr]; exists r; intro x.
    rewrite !qeval_sub; specialize (Hr x); rewrite qeval_sub in Hr.
    replace (qeval a x - qeval c x - (qeval a' x - qeval c x))
       with (qeval a x - qeval a' x) by ring; rewrite Hr; ring.
  Qed.

  Lemma rsum_split : forall f a b,
    Rq (rsum f (a + b)%nat) (qadd (rsum f a) (rsum (fun i => f (a + i)%nat) b)).
  Proof.
    intros f a b; induction b as [|b IH].
    - replace (a + 0)%nat with a by lia; cbn [rsum].
      apply req_of_qeval; intro x; rewrite qeval_add, qeval_nil; ring.
    - replace (a + S b)%nat with (S (a + b))%nat by lia; cbn [rsum].
      apply (req_trans Nn _ (qadd (qadd (rsum f a) (rsum (fun i => f (a + i)%nat) b)) (f (a + b)%nat)) _).
      + apply req_qadd; [ exact IH | apply req_refl ].
      + apply req_of_qeval; intro x; rewrite !qeval_add; ring.
  Qed.

  (* generic geometric identity: (ρ−1)·Σ_{r<len} ρ^r = ρ^len − 1 *)
  Lemma geom_qeval : forall rho len x,
    qeval (qmul (qsub rho [1]) (rsum (fun r => rpow rho r) len)) x = (qeval rho x) ^ len - 1.
  Proof.
    intros rho len x; induction len as [|len IH]; cbn [rsum rpow].
    - rewrite qeval_mul, qeval_nil; cbn [Qcpower]; rewrite qeval_sub, qeval_one; ring.
    - rewrite qeval_mul, qeval_add, qeval_rpow, qeval_sub, qeval_one.
      rewrite qeval_mul, qeval_sub, qeval_one in IH.
      set (R := qeval rho x) in *; set (s := qeval (rsum (fun r => rpow rho r) len) x) in *.
      cbn [Qcpower].
      replace ((R - 1) * (s + R ^ len)) with ((R - 1) * s + (R - 1) * R ^ len) by ring.
      rewrite IH; ring.
  Qed.

  Lemma geom_len : forall rho len,
    Rq (qmul (qsub rho [1]) (rsum (fun r => rpow rho r) len)) (qsub (rpow rho len) [1]).
  Proof.
    intros rho len; apply req_of_qeval; intro x.
    rewrite geom_qeval, qeval_sub, qeval_rpow, qeval_one; reflexivity.
  Qed.

  Lemma geom_vanish : forall rho len,
    Rq (rpow rho len) [1] -> (exists u, Rq (qmul u (qsub rho [1])) [1]) ->
    Rq (rsum (fun r => rpow rho r) len) [].
  Proof.
    intros rho len Hpow Hunit.
    apply (vanish_helper Nn (qsub rho [1]) (rsum (fun r => rpow rho r) len)).
    - apply (req_trans Nn _ (qsub (rpow rho len) [1]) _);
        [ apply geom_len | apply req_sub_nil; exact Hpow ].
    - exact Hunit.
  Qed.

  Lemma geom_triv : forall rho len,
    Rq rho [1] -> Rq (rsum (fun r => rpow rho r) len) (qconst (qnat len)).
  Proof.
    intros rho len Hr.
    apply (req_trans Nn _ (rsum (fun _ => [1]) len) _).
    - apply (rsum_ext_bounded Nn HNg); intros r _.
      apply (req_trans Nn _ (rpow [1] r) _);
        [ apply req_rpow; exact Hr
        | apply req_of_qeval; intro x; rewrite qeval_rpow, !qeval_one, Qcpow_1_l; reflexivity ].
    - apply req_of_qeval; intro x; rewrite rsum_ones, qeval_const; reflexivity.
  Qed.

  (* generalized unit: ζ^E − 1 is a unit whenever E mod N ≠ 0 *)
  Lemma zeta_sub_unit_gen : forall E, (E mod Nn <> 0)%nat ->
    exists u, Rq (qmul u (qsub (rpow zeta E) [1])) [1].
  Proof.
    intros E HE.
    assert (Hlt : (0 < E mod Nn < Nn)%nat)
      by (split; [ apply Nat.neq_0_lt_0; exact HE | apply Nat.mod_upper_bound; lia ]).
    destruct (zeta_pow_sub_unit Nn HNg (E mod Nn) Hlt) as [u Hu].
    exists u.
    apply (req_trans Nn _ (qmul u (qsub (rpow zeta (E mod Nn)) [1])) _); [ | exact Hu ].
    apply req_qmul_l, req_sub_l, (rpow_base_periodic Nn zeta (zeta_pow_N Nn HNg)).
  Qed.

  (* the block-delta:  Σ_{i<len} h i · [i=0] c  ≡  h 0 · c  (len > 0) *)
  Lemma rsum_delta0 : forall (h : nat -> qpoly) c len, (0 < len)%nat ->
    Rq (rsum (fun i => qmul (h i) (if (i =? 0)%nat then c else [])) len) (qmul (h 0%nat) c).
  Proof.
    intros h c len Hlen.
    apply (req_trans Nn _ (rsum (fun i => if (0 =? i)%nat then qmul (h 0%nat) c else []) len) _).
    - apply (rsum_ext_bounded Nn HNg); intros i _; destruct i; cbn [Nat.eqb];
        [ apply req_refl | apply req_of_qeval; intro x; rewrite qeval_mul, qeval_nil; ring ].
    - apply (req_trans Nn _ (if (0 <? len)%nat then qmul (h 0%nat) c else []) _).
      + apply (rsum_delta Nn HNg (fun _ => qmul (h 0%nat) c) len 0).
      + destruct (Nat.ltb_spec 0 len); [ apply req_refl | lia ].
  Qed.

  (* the reindex k = a·mm + b, keeping only b = 0 *)
  Lemma sum_multiples_R : forall (g : nat -> qpoly) D mm, (0 < mm)%nat ->
    Rq (rsum (fun k => qmul (g k) (if (k mod mm =? 0)%nat then qconst (qnat mm) else [])) (D * mm))
       (qmul (qconst (qnat mm)) (rsum (fun a => g (a * mm)%nat) D)).
  Proof.
    intros g D mm Hmm; induction D as [|D IH].
    - replace (0 * mm)%nat with 0%nat by lia; cbn [rsum].
      apply req_of_qeval; intro x; rewrite qeval_mul, !qeval_nil; ring.
    - replace (S D * mm)%nat with (D * mm + mm)%nat by lia.
      apply (req_trans Nn _
        (qadd (rsum (fun k => qmul (g k) (if (k mod mm =? 0)%nat then qconst (qnat mm) else [])) (D * mm))
              (rsum (fun i => qmul (g (D * mm + i)%nat)
                 (if ((D * mm + i) mod mm =? 0)%nat then qconst (qnat mm) else [])) mm)) _).
      { apply rsum_split. }
      (* the block reduces to g(D·mm)·mm via rsum_delta0 *)
      apply (req_trans Nn _
        (qadd (qmul (qconst (qnat mm)) (rsum (fun a => g (a * mm)%nat) D))
              (qmul (g (D * mm)%nat) (qconst (qnat mm)))) _).
      { apply req_qadd.
        - exact IH.
        - apply (req_trans Nn _
            (rsum (fun i => qmul (g (D * mm + i)%nat) (if (i =? 0)%nat then qconst (qnat mm) else [])) mm) _).
          + apply (rsum_ext_bounded Nn HNg); intros i Hi.
            replace ((D * mm + i) mod mm)%nat with i
              by (rewrite Nat.add_comm, Nat.Div0.mod_add; symmetry; apply Nat.mod_small; lia);
              apply req_refl.
          + apply (req_trans Nn _ (qmul (g (D * mm + 0)%nat) (qconst (qnat mm))) _);
              [ apply (rsum_delta0 (fun i => g (D * mm + i)%nat) (qconst (qnat mm)) mm Hmm)
              | replace (D * mm + 0)%nat with (D * mm)%nat by lia; apply req_refl ]. }
      (* fold the new block into the scaled sum *)
      apply (req_trans Nn _
        (qmul (qconst (qnat mm)) (qadd (rsum (fun a => g (a * mm)%nat) D) (g (D * mm)%nat))) _).
      + apply req_of_qeval; intro x; rewrite !qeval_add, !qeval_mul, ?qeval_add; ring.
      + apply req_qmul_l; apply req_refl.
  Qed.

End RGeneric.

(* the length-m orthogonality inside the modulus-(d·m) ring *)
Lemma orth_val_R : forall d m, (0 < d)%nat -> (0 < m)%nat -> forall k,
  req (d * m) (rsum (fun r => rpow (wcz (d * m)) (r * d * k)) m)
              (if (k mod m =? 0)%nat then qconst (qnat m) else []).
Proof.
  intros d m Hd Hm k. assert (Hnn : (1 <= d * m)%nat) by nia.
  Local Open Scope Qc_scope.
  (* rewrite each summand as ρ^r with ρ = wcz(dm)^{d·k} *)
  apply (req_trans (d * m) _ (rsum (fun r => rpow (rpow (wcz (d * m)) (d * k)) r) m) _).
  { apply (rsum_ext_bounded (d * m) Hnn); intros r _.
    apply req_of_qeval; intro x; rewrite !qeval_rpow, <- Qcpow_mul; f_equal; nia. }
  (* ρ^m ≡ 1 *)
  assert (Hpm : req (d * m) (rpow (rpow (wcz (d * m)) (d * k)) m) [1]).
  { apply (req_trans (d * m) _ (rpow (rpow (wcz (d * m)) (d * m)) k) _).
    - apply req_of_qeval; intro x; rewrite !qeval_rpow, <- !Qcpow_mul; f_equal; nia.
    - apply (req_trans (d * m) _ (rpow [1] k) _);
        [ apply req_rpow, (wcz_pow_N (d * m) Hnn)
        | apply req_of_qeval; intro x; rewrite qeval_rpow, !qeval_one, Qcpow_1_l; reflexivity ]. }
  destruct (Nat.eqb_spec (k mod m) 0) as [Hk0 | Hk0].
  - (* m | k : ρ ≡ 1, geometric = m·1 *)
    apply geom_triv; [ exact Hnn | ].
    apply (req_trans (d * m) _ (rpow (rpow (wcz (d * m)) (d * m)) (k / m)) _).
    + apply req_of_qeval; intro x; rewrite !qeval_rpow, <- Qcpow_mul; f_equal.
      pose proof (Nat.div_mod_eq k m); nia.
    + apply (req_trans (d * m) _ (rpow [1] (k / m)) _);
        [ apply req_rpow, (wcz_pow_N (d * m) Hnn)
        | apply req_of_qeval; intro x; rewrite qeval_rpow, !qeval_one, Qcpow_1_l; reflexivity ].
  - (* m ∤ k : ρ − 1 is a unit, geometric = 0 *)
    apply (geom_vanish (d * m)); [ exact Hpm | ].
    (* ρ ≡ ζ^{(dm−1)·d·k};  its E mod (dm) ≠ 0 ⟺ m ∤ k *)
    assert (HEmod : (((d * m - 1) * (d * k)) mod (d * m) <> 0)%nat).
    { intro Hc. apply Nat.Lcm0.mod_divide in Hc; destruct Hc as [c Hc].
      assert (Hdk : ((d * m) * (d * k) = d * k + (d * m) * c)%nat) by nia.
      assert (Hdiv : Nat.divide (d * m) (d * k)) by (exists (d * k - c)%nat; nia).
      destruct Hdiv as [e He]; apply Hk0.
      assert (Hke : (k = e * m)%nat) by nia; subst k.
      rewrite Nat.Div0.mod_mul; reflexivity. }
    destruct (zeta_sub_unit_gen (d * m) Hnn ((d * m - 1) * (d * k)) HEmod) as [u Hu].
    exists u.
    apply (req_trans (d * m) _ (qmul u (qsub (rpow zeta ((d * m - 1) * (d * k))) [1])) _); [ | exact Hu ].
    apply req_qmul_l, req_sub_l.
    unfold wcz; apply req_of_qeval; intro x; rewrite !qeval_rpow, <- Qcpow_mul; f_equal; nia.
Qed.

Theorem finite_poisson_R : forall d m (f : nat -> qpoly), (0 < d)%nat -> (0 < m)%nat ->
  req (d * m) (rsum (fun r => DFT_R (d * m) f (r * d)) m)
              (qmul (qconst (qnat m)) (rsum (fun a => f (a * m)%nat) d)).
Proof.
  intros d m f Hd Hm. assert (Hnn : (1 <= d * m)%nat) by nia.
  Local Open Scope Qc_scope.
  unfold DFT_R.
  apply (req_trans (d * m) _
    (rsum (fun k => rsum (fun r => qmul (f k) (rpow (wcz (d * m)) (r * d * k))) m) (d * m)) _).
  { apply (rsum_swap (d * m) (fun r k => qmul (f k) (rpow (wcz (d * m)) (r * d * k))) m (d * m)). }
  apply (req_trans (d * m) _
    (rsum (fun k => qmul (f k) (if (k mod m =? 0)%nat then qconst (qnat m) else [])) (d * m)) _).
  { apply (rsum_ext_bounded (d * m) Hnn); intros k _.
    apply (req_trans (d * m) _ (qmul (f k) (rsum (fun r => rpow (wcz (d * m)) (r * d * k)) m)) _).
    - apply req_sym, (rsum_scale_l (d * m)).
    - apply req_qmul_l, (orth_val_R d m Hd Hm k). }
  apply (sum_multiples_R (d * m) Hnn f d m Hm).
Qed.

Print Assumptions finite_poisson_R.

(* ================================================================= *)
(*  END FinitePoisson.v.  Σ_{r<m}(DFT_N f)(rd) = m·Σ_{a<d}f(am),      *)
(*  N=dm — the finite Poisson summation formula.                     *)
(* ================================================================= *)

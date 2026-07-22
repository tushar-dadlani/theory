(* ================================================================= *)
(*  RootsOfUnity.v                                                   *)
(*                                                                    *)
(*  THE N-TH ROOTS OF UNITY in the custom complex field C = R[i]      *)
(*  (ComplexField), and the DFT ORTHOGONALITY relation they satisfy.  *)
(*                                                                    *)
(*    w N   :=  exp(2 pi i / N)  =  cos(2pi/N) + i sin(2pi/N)          *)
(*                                                                    *)
(*    w_pow_N            : (w N)^N = 1        (it IS an N-th root)     *)
(*    de_moivre          : (cos t + i sin t)^n = cos(nt) + i sin(nt)   *)
(*    geom_sum           : (a-1) * sum_{k<N} a^k = a^N - 1  (telescope) *)
(*    dft_orthogonality  : sum_{k<N} ((w N)^j)^k                       *)
(*                            = N   if (w N)^j = 1                     *)
(*                            = 0   otherwise                          *)
(*                                                                    *)
(*  This is the complex-DFT orthogonality: the character sums over the *)
(*  roots of unity are N (trivial character) or 0 (nontrivial) -- the  *)
(*  general-N generalisation of WalshHadamard's H^2 = 8 I on F_2^3.    *)
(*  The "= 0" branch rests only on a^N = 1 (so a^N - 1 = 0) plus the    *)
(*  geometric-series telescoping -- pure field algebra in C; the trig  *)
(*  (De Moivre + cos/sin at 2pi) enters ONLY to prove (w N)^N = 1.     *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via C over R and the *)
(*  trig functions cos/sin/PI).                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField.   (* imported last so ComplexField.C shadows Reals' binomial C *)
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Complex powers and finite sums                                   *)
(* ----------------------------------------------------------------- *)

Fixpoint Cpow (a : C) (n : nat) : C :=
  match n with O => C1 | S k => Cmul a (Cpow a k) end.

Fixpoint Csum (f : nat -> C) (n : nat) : C :=
  match n with O => C0 | S k => Cadd (Csum f k) (f k) end.

Lemma Cpow_add : forall a m n, Cpow a (m + n) = Cmul (Cpow a m) (Cpow a n).
Proof.
  intros a m n; induction m as [|m IH]; cbn [Cpow Nat.add].
  - ring.
  - rewrite IH; ring.
Qed.

Lemma Cpow_mul : forall a m n, Cpow a (m * n) = Cpow (Cpow a m) n.
Proof.
  intros a m n; induction n as [|n IH].
  - rewrite Nat.mul_0_r; reflexivity.
  - rewrite Nat.mul_succ_r, Cpow_add, IH; cbn [Cpow]; ring.
Qed.

Lemma Cpow_C1 : forall k, Cpow C1 k = C1.
Proof. induction k as [|k IH]; [ reflexivity | cbn [Cpow]; rewrite IH; ring ]. Qed.

Lemma Csum_ext : forall f g N, (forall k, f k = g k) -> Csum f N = Csum g N.
Proof.
  intros f g N H; induction N as [|N IH];
    cbn [Csum]; [ reflexivity | rewrite IH, H; reflexivity ].
Qed.

(* ----------------------------------------------------------------- *)
(*  DE MOIVRE  (cos t + i sin t)^n = cos(nt) + i sin(nt)             *)
(* ----------------------------------------------------------------- *)

Lemma de_moivre : forall theta n,
  Cpow (mkC (cos theta) (sin theta)) n
  = mkC (cos (INR n * theta)) (sin (INR n * theta)).
Proof.
  intros theta n; induction n as [|n IH].
  - apply Ceq; cbn [Cpow C1 Re Im]; simpl INR; rewrite Rmult_0_l;
      [ rewrite cos_0; reflexivity | rewrite sin_0; reflexivity ].
  - cbn [Cpow]; rewrite IH; apply Ceq; cbn [Cmul Re Im]; rewrite S_INR;
      replace ((INR n + 1) * theta) with (theta + INR n * theta) by ring;
      [ rewrite cos_plus; ring | rewrite sin_plus; ring ].
Qed.

(* ----------------------------------------------------------------- *)
(*  THE N-TH ROOT OF UNITY  w N = exp(2 pi i / N)                     *)
(* ----------------------------------------------------------------- *)

Definition w (N : nat) : C := mkC (cos (2 * PI / INR N)) (sin (2 * PI / INR N)).

Theorem w_pow_N : forall N, (0 < N)%nat -> Cpow (w N) N = C1.
Proof.
  intros N HN.
  unfold w; rewrite de_moivre.
  assert (HNr : INR N <> 0) by (apply not_0_INR; lia).
  assert (Heq : INR N * (2 * PI / INR N) = 2 * PI) by (field; exact HNr).
  rewrite Heq; apply Ceq; cbn [C1 Re Im]; [ apply cos_2PI | apply sin_2PI ].
Qed.

(* ----------------------------------------------------------------- *)
(*  GEOMETRIC SERIES  (a-1) * sum_{k<N} a^k = a^N - 1  (pure C algebra) *)
(* ----------------------------------------------------------------- *)

Lemma geom_sum : forall a N,
  Cmul (Cminus a C1) (Csum (fun k => Cpow a k) N) = Cminus (Cpow a N) C1.
Proof.
  intros a N; induction N as [|N IH].
  - cbn [Csum Cpow]; ring.
  - cbn [Csum Cpow].
    replace (Cmul (Cminus a C1) (Cadd (Csum (fun k => Cpow a k) N) (Cpow a N)))
      with  (Cadd (Cmul (Cminus a C1) (Csum (fun k => Cpow a k) N))
                  (Cmul (Cminus a C1) (Cpow a N))) by ring.
    rewrite IH; ring.
Qed.

Lemma geom_sum_value : forall a N, a <> C1 ->
  Csum (fun k => Cpow a k) N = Cdiv (Cminus (Cpow a N) C1) (Cminus a C1).
Proof.
  intros a N Ha.
  assert (Hne : Cminus a C1 <> C0).
  { intro H; apply Ha.
    unfold Cminus, C1, C0 in H; injection H as HRe HIm.
    apply Ceq; cbn [C1 Re Im]; lra. }
  rewrite <- geom_sum; field; exact Hne.
Qed.

(* ----------------------------------------------------------------- *)
(*  CHARACTER SUMS: the two branches                                 *)
(* ----------------------------------------------------------------- *)

Lemma Csum_const_C1 : forall N, Csum (fun _ => C1) N = RtoC (INR N).
Proof.
  induction N as [|N IH].
  - cbn [Csum]; apply Ceq; cbn [C0 RtoC Re Im]; simpl INR; reflexivity.
  - cbn [Csum]; rewrite IH, S_INR;
      apply Ceq; cbn [RtoC Cadd C1 Re Im]; ring.
Qed.

Lemma sum_pow_eq_1 : forall a N, a = C1 ->
  Csum (fun k => Cpow a k) N = RtoC (INR N).
Proof.
  intros a N Ha; subst a.
  rewrite (Csum_ext (fun k => Cpow C1 k) (fun _ => C1) N (fun k => Cpow_C1 k)).
  apply Csum_const_C1.
Qed.

Lemma sum_pow_eq_0 : forall a N, a <> C1 -> Cpow a N = C1 ->
  Csum (fun k => Cpow a k) N = C0.
Proof.
  intros a N Ha HaN.
  rewrite geom_sum_value by exact Ha.
  rewrite HaN.
  replace (Cminus C1 C1) with C0 by ring.
  unfold Cdiv; ring.
Qed.

(* decidable equality on C (componentwise, via classical Req_dec_T) *)
Definition Ceq_dec (a b : C) : {a = b} + {a <> b}.
Proof.
  destruct (Req_dec_T (Re a) (Re b)) as [HR|HR];
    destruct (Req_dec_T (Im a) (Im b)) as [HI|HI].
  - left; apply Ceq; assumption.
  - right; intro H; apply HI; rewrite H; reflexivity.
  - right; intro H; apply HR; rewrite H; reflexivity.
  - right; intro H; apply HR; rewrite H; reflexivity.
Defined.

(* ----------------------------------------------------------------- *)
(*  THE DFT ORTHOGONALITY RELATION                                   *)
(* ----------------------------------------------------------------- *)

Theorem dft_orthogonality : forall N j, (0 < N)%nat ->
  Csum (fun k => Cpow (Cpow (w N) j) k) N
  = (if Ceq_dec (Cpow (w N) j) C1 then RtoC (INR N) else C0).
Proof.
  intros N j HN.
  destruct (Ceq_dec (Cpow (w N) j) C1) as [Heq | Hne].
  - apply sum_pow_eq_1; exact Heq.
  - apply sum_pow_eq_0; [ exact Hne | ].
    (* (w N ^ j)^N = (w N ^ N)^j = 1^j = 1 *)
    rewrite <- Cpow_mul, Nat.mul_comm, Cpow_mul, (w_pow_N N HN).
    apply Cpow_C1.
Qed.

(* ----------------------------------------------------------------- *)
(*  PRIMITIVITY:  (w N)^j <> 1  for  0 < j < N                        *)
(*                                                                    *)
(*  The one real-analysis input.  (w N)^j = cos(2pi j/N) + i sin(...), *)
(*  and for 0 < 2pi j/N < 2pi we have cos(2pi j/N) < 1 strictly (via   *)
(*  cos x = 1 - 2 sin^2(x/2) and sin(x/2) > 0 on (0, pi)), so it       *)
(*  cannot equal 1.                                                   *)
(* ----------------------------------------------------------------- *)

Lemma cos_lt_1 : forall x, 0 < x -> x < 2 * PI -> cos x < 1.
Proof.
  intros x Hx0 Hx2.
  assert (Hs : 0 < sin (x / 2)) by (apply sin_gt_0; lra).
  replace x with (2 * (x / 2)) by field.
  rewrite cos_2a_sin; nra.
Qed.

Theorem w_primitive : forall N j, (0 < j < N)%nat -> Cpow (w N) j <> C1.
Proof.
  intros N j [Hj0 HjN].
  assert (HjR  : 0 < INR j)      by (apply lt_0_INR; lia).
  assert (HNR  : 0 < INR N)      by (apply lt_0_INR; lia).
  assert (HjltN: INR j < INR N)  by (apply lt_INR; lia).
  assert (HPI  : 0 < PI)         by exact PI_RGT_0.
  assert (Hne  : INR N <> 0)     by (apply Rgt_not_eq; exact HNR).
  unfold w; rewrite de_moivre; intro H.
  assert (Hcos : cos (INR j * (2 * PI / INR N)) = 1) by exact (f_equal Re H).
  assert (Hlo : 0 < INR j * (2 * PI / INR N)).
  { apply Rmult_lt_0_compat; [ exact HjR | ].
    unfold Rdiv; apply Rmult_lt_0_compat; [ lra | apply Rinv_0_lt_compat; exact HNR ]. }
  assert (Hhi : INR j * (2 * PI / INR N) < 2 * PI).
  { replace (INR j * (2 * PI / INR N)) with (2 * PI * (INR j / INR N)) by (field; exact Hne).
    rewrite <- (Rmult_1_r (2 * PI)) at 2.
    apply Rmult_lt_compat_l; [ lra | ].
    apply Rmult_lt_reg_r with (INR N); [ exact HNR | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by exact Hne.
    rewrite Rmult_1_r, Rmult_1_l; exact HjltN. }
  pose proof (cos_lt_1 _ Hlo Hhi) as Hlt; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  DFT ORTHOGONALITY, unconditional Kronecker-delta form            *)
(*     sum_{k<N} (w N)^{jk}  =  N   if j = 0                          *)
(*                          =  0   if 0 < j < N                       *)
(* ----------------------------------------------------------------- *)

Theorem dft_orthogonality_delta : forall N j, (j < N)%nat ->
  Csum (fun k => Cpow (Cpow (w N) j) k) N
  = (if Nat.eqb j 0 then RtoC (INR N) else C0).
Proof.
  intros N j HjN; destruct (Nat.eqb j 0) eqn:E.
  - apply Nat.eqb_eq in E; subst j.
    apply sum_pow_eq_1; reflexivity.
  - apply Nat.eqb_neq in E.
    apply sum_pow_eq_0; [ apply w_primitive; lia | ].
    rewrite <- Cpow_mul, Nat.mul_comm, Cpow_mul, (w_pow_N N ltac:(lia)).
    apply Cpow_C1.
Qed.

Print Assumptions w_pow_N.
Print Assumptions w_primitive.
Print Assumptions dft_orthogonality_delta.

(* ================================================================= *)
(*  END RootsOfUnity.v                                               *)
(*  The N-th roots of unity w N = exp(2 pi i/N) in the custom field    *)
(*  C = R[i]: w_pow_N proves (w N)^N = 1 (via De Moivre + cos/sin at   *)
(*  2 pi), and dft_orthogonality proves the character-sum relation     *)
(*  sum_{k<N} (w N)^{jk} = N or 0 -- the complex-DFT orthogonality,    *)
(*  general-N cousin of WalshHadamard's H^2 = 8 I.  The vanishing      *)
(*  branch is pure field algebra (geometric series + a^N = 1); only    *)
(*  (w N)^N = 1 uses the trig / Reals axioms (quarantined).           *)
(* ================================================================= *)

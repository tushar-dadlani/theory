(* ================================================================= *)
(*  SelbergRForm.v  —  Selberg's inequality in remainder (R) form.     *)
(*                                                                    *)
(*  Psiform N := psi(N) ln N + Sum_{d<=N} Lam(d) psi(floor(N/d))        *)
(*  Rform  N := R(N) ln N   + Sum_{d<=N} Lam(d) R(floor(N/d)),          *)
(*      R = Rem = psi - id.                                             *)
(*                                                                    *)
(*  The EXACT unconditional identity                                    *)
(*      Psiform N = Rform N + N ln N + Tlog N                           *)
(*  (using psi = N + R and Sum Lam(d) floor(N/d) = Tlog N =             *)
(*   order_swap_identity) reduces Selberg's psi-form inequality         *)
(*      | Psiform N - 2 N ln N | <= C N                                 *)
(*  to the self-improving R-form                                        *)
(*      | Rform N | <= (C+1) N,                                         *)
(*  since | N ln N - Tlog N | <= N (the Stirling bracket).  This is the  *)
(*  inequality the Erdos-Selberg averaging argument bootstraps on.      *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        MertensVonMangoldt SelbergSymmetry SelbergEndgame.
Import ListNotations.
Open Scope R_scope.

Definition Psiform (N : nat) : R :=
  psi N * ln (INR N) + Rls (seq 1 N) (fun d => Lam d * psi (N / d)%nat).
Definition Rform (N : nat) : R :=
  Rem N * ln (INR N) + Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat).

(* the exact algebraic identity connecting the two *)
Theorem selberg_identity : forall N,
  Psiform N = Rform N + INR N * ln (INR N) + Tlog N.
Proof.
  intro N; unfold Psiform, Rform.
  assert (Hsum : Rls (seq 1 N) (fun d => Lam d * psi (N / d)%nat)
               = chsum N + Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat)).
  { rewrite (Rls_ext _ (fun d => Lam d * psi (N / d)%nat)
               (fun d => Lam d * INR (N / d)%nat + Lam d * Rem (N / d)%nat) (seq 1 N))
      by (intros d _; unfold Rem; ring).
    rewrite Rls_add.
    replace (Rls (seq 1 N) (fun d => Lam d * INR (N / d)%nat)) with (chsum N)
      by (unfold chsum, Rls; reflexivity).
    reflexivity. }
  rewrite Hsum, <- (order_swap_identity N).
  unfold Rem; ring.
Qed.

(* the Stirling bracket, packaged *)
Lemma Tlog_close : forall N, (1 <= N)%nat ->
  Rabs (INR N * ln (INR N) - Tlog N) <= INR N.
Proof.
  intros N HN; pose proof (Tlog_upper N); pose proof (Tlog_lower N HN);
    pose proof (pos_INR N); apply Rabs_le; split; lra.
Qed.

(* the reduction:  psi-form Selberg inequality  ==>  R-form inequality *)
Theorem selberg_R_form : forall C,
  (forall N, (1 <= N)%nat -> Rabs (Psiform N - 2 * INR N * ln (INR N)) <= C * INR N) ->
  forall N, (1 <= N)%nat -> Rabs (Rform N) <= (C + 1) * INR N.
Proof.
  intros C Hpsi N HN.
  pose proof (selberg_identity N) as Hid.
  pose proof (Tlog_close N HN) as Hcl.
  pose proof (Hpsi N HN) as Hp.
  assert (HR : Rform N
             = (Psiform N - 2 * INR N * ln (INR N)) + (INR N * ln (INR N) - Tlog N))
    by lra.
  rewrite HR.
  eapply Rle_trans; [ apply Rabs_triang | lra ].
Qed.

Print Assumptions selberg_R_form.

(* ================================================================= *)
(*  END SelbergRForm.v                                                *)
(*  | R(N) ln N + Sum_{d<=N} Lam(d) R(floor(N/d)) | <= (C+1) N,         *)
(*  given Selberg's psi-form  | Psiform N - 2 N ln N | <= C N.          *)
(* ================================================================= *)

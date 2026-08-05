(* ================================================================= *)
(*  ErdosSelberg.v  —  the entry inequality to the limit argument (Step 3).*)
(*                                                                    *)
(*  From the unconditional Selberg inequality                          *)
(*      | R(N) ln N + Sum_{d<=N} Lam(d) R(floor(N/d)) | <= C N,         *)
(*  the triangle inequality (with Lam >= 0, ln N >= 0) gives the        *)
(*  self-referential bound the Erdos-Selberg averaging argument         *)
(*  bootstraps on:                                                     *)
(*      |R(N)| ln N <= Sum_{d<=N} Lam(d) |R(floor(N/d))| + C N.         *)
(*  (R(N) = psi(N) - N; C = 89 + 3 Kup.)  Axiom-clean.                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import VonMangoldtGlobal RealMobius Chebyshev ChebyshevBound
        MobiusOverD SelbergEndgame SelbergRForm SelbergPsiForm.
Import ListNotations.
Open Scope R_scope.

Theorem selberg_Rabs : forall N, (1 <= N)%nat ->
  Rabs (Rem N) * ln (INR N)
  <= Rls (seq 1 N) (fun d => Lam d * Rabs (Rem (N / d)%nat))
     + (88 + 3 * Kup + 1) * INR N.
Proof.
  intros N HN.
  pose proof (selberg_inequality N HN) as HS.
  assert (Hform : Rem N * ln (INR N)
                = Rform N - Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat))
    by (unfold Rform; ring).
  assert (Habs1 : Rabs (Rem N * ln (INR N)) = Rabs (Rem N) * ln (INR N)).
  { rewrite Rabs_mult; f_equal; apply Rabs_pos_eq; apply lpos; exact HN. }
  assert (Habs2 : Rabs (Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat))
                <= Rls (seq 1 N) (fun d => Lam d * Rabs (Rem (N / d)%nat))).
  { eapply Rle_trans; [ apply Rls_abs | ].
    apply Rls_le; intros d _.
    rewrite Rabs_mult, (Rabs_pos_eq (Lam d)) by apply Lam_nonneg; apply Rle_refl. }
  rewrite <- Habs1, Hform.
  replace (Rform N - Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat))
    with (Rform N + (- Rls (seq 1 N) (fun d => Lam d * Rem (N / d)%nat))) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ]; rewrite Rabs_Ropp.
  apply Rle_trans with
    ((88 + 3 * Kup + 1) * INR N
     + Rls (seq 1 N) (fun d => Lam d * Rabs (Rem (N / d)%nat))).
  - apply Rplus_le_compat; [ exact HS | exact Habs2 ].
  - lra.
Qed.

Print Assumptions selberg_Rabs.

(* ================================================================= *)
(*  END ErdosSelberg.v  —  |R(N)| ln N <= Sum Lam(d)|R(floor(N/d))| + C N.*)
(* ================================================================= *)

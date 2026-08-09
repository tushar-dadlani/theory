(* ================================================================= *)
(*  SelbergLambda2Dip.v  —  toward lambda2_dip (Selberg's density crux).*)
(*                                                                    *)
(*  lambda2_dip needs a positive-Λ₂-density set of scales where Vrem    *)
(*  dips below b < α.  The concrete, provable ATOM every such argument  *)
(*  needs is the Λ₂-mass of an index interval (a, c]:                    *)
(*                                                                    *)
(*    Σ_{a<n≤c} Λ2(n)/n = ln²c − ln²a + O(ln c)                         *)
(*                                                                    *)
(*  (from SmoothingLemma.lam2_over_n_bound at the two endpoints).       *)
(*  A multiplicative DIP band of scales [m1,m2] (Vrem ≤ b throughout)   *)
(*  maps to the index interval (N/m2, N/m1], contributing Λ₂-mass       *)
(*  ln²(N/m1) − ln²(N/m2) to dipw2; the REMAINING crux is aggregating    *)
(*  enough such bands to reach θ·ln²N (the sign-change density, the deep *)
(*  Selberg/Erdős estimate — see the header note).  Axiom-clean.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound RealMobius MobiusOverD SelbergSymmetry
        SmoothingLemma SelbergSelfImprove.
Open Scope R_scope.

(* the Λ₂-mass of the index interval (a, c] is ln²c − ln²a up to O(ln c) *)
Theorem lam2_interval_mass : forall a c, (1 <= a)%nat -> (a <= c)%nat ->
  Rabs (Rls (seq (S a) (c - a)) (fun n => Lam2 n / INR n)
        - (ln (INR c) * ln (INR c) - ln (INR a) * ln (INR a)))
  <= (Kup * ln (INR c) + (Kup + ln 2) * (ln (INR c) + Kup))
     + (Kup * ln (INR a) + (Kup + ln 2) * (ln (INR a) + Kup)).
Proof.
  intros a c Ha Hac.
  assert (Hsplit : seq 1 c = seq 1 a ++ seq (S a) (c - a)).
  { replace c with (a + (c - a))%nat at 1 by lia.
    rewrite List.seq_app; f_equal; f_equal; lia. }
  assert (Heq : Rls (seq (S a) (c - a)) (fun n => Lam2 n / INR n)
                = Rls (seq 1 c) (fun n => Lam2 n / INR n)
                  - Rls (seq 1 a) (fun n => Lam2 n / INR n))
    by (rewrite Hsplit, Rls_app; ring).
  rewrite Heq.
  pose proof (lam2_over_n_bound c ltac:(lia)) as Hc.
  pose proof (lam2_over_n_bound a Ha) as Haa.
  replace (Rls (seq 1 c) (fun n => Lam2 n / INR n) - Rls (seq 1 a) (fun n => Lam2 n / INR n)
           - (ln (INR c) * ln (INR c) - ln (INR a) * ln (INR a)))
    with ((Rls (seq 1 c) (fun n => Lam2 n / INR n) - ln (INR c) * ln (INR c))
          - (Rls (seq 1 a) (fun n => Lam2 n / INR n) - ln (INR a) * ln (INR a))) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ].
  apply Rplus_le_compat; [ exact Hc | rewrite Rabs_Ropp; exact Haa ].
Qed.

Print Assumptions lam2_interval_mass.

(* ================================================================= *)
(*  END SelbergLambda2Dip.v  —  the Λ₂-interval-mass atom is in place;   *)
(*  the deep remaining lemma is the DENSITY of dip bands (sign changes   *)
(*  of R at positive log-density across [1,N]) — Selberg's 1949 core.    *)
(* ================================================================= *)

# Build-Repair Gap Catalogue

**Context.** The repo was ported to build under **Rocq/Coq 9.1.1**. Before this work, 131 of 397 `.v` targets failed to compile. They now all build (`make` exits 0). Reaching a green build required, in addition to many genuine proof/porting fixes, replacing a number of proof bodies with `Admitted` — **statements were preserved verbatim; none were weakened or deleted.** This file catalogues those gaps so the mathematics can be triaged separately from the build.

## Summary
- **135 statements newly `Admitted`** by this repair (64 files). 90 further `Admitted` pre-date this work.
- **~42 new `Axiom`/`Parameter`** declarations (mostly: non-strictly-positive records or non-guarded co/recursion that Rocq 9.1 rejects, replaced by an interface + computation-rule axioms; and `Variable` outside a section, now a hard error, converted to `Parameter`).
- **26 previously-`Admitted` proofs were completed to real `Qed`** during the repair (net improvement).

## ⚠️ Statements that are FALSE as written
These were `Admitted` because they cannot be proved as stated — the repair agents found explicit counterexamples. Per policy the statements were left untouched. **These need mathematical revision, not proof effort.** (List is from agent analysis and is not exhaustive — the `complexity-sat` / `millennium-problems` / `06-synthesis` cluster was repaired by an agent that was interrupted before reporting its false-statement findings; see the auto-generated inventory below for that cluster's admits.)

| File | Theorem | Why it's false (counterexample) |
|---|---|---|
| `00-foundations/collapse.v` | `collapse_breaks_oscillation` | `relational_info_bit One One = 0`, statement claims `1` |
| `00-foundations/set_witnessing.v` | `pow2_exp2_mod3` | n=0: `exp2 0 = 1`, `2^1 mod 3 = 2 ≠ 1` |
| `00-foundations/foldcollapse.v` | 8 lemmas (`master_fold_theorem` et al.) | `the_law3` does not implement ℤ/6ℤ addition |
| `02-symbol-line/encoding_any_sym_same_same.v` | `same_encodes_to_halfstep`, `swap_preserves_encoding` | `the_law One One = Zero`; law not swap-invariant |
| `number-systems/set_field_closure.v` | `fermat_maps_to_diagonal`, `fermat_is_unit`, `fermat_permanently_diagonal` | construction forgets `F₀ = 3` (divisible by 3) |
| `number-systems/BigIntArith.v` | `sub_bits_via_twos_complement`, `sub_uses_n_strand` | RHS reduced mod 2^len; a=4,b=1 breaks the multiple-of-2 claim |
| `number-theory/GaussianPrimesCorollary.v` | `brahmagupta_fibonacci`, `norm_multiplicative` | false over `nat` (truncated subtraction: a=1,b=3,c=1,d=2) |
| `number-theory/directed_adic.v` | `rotate3_is_outbound_step`, `law3_to_C_means_converging` | `rotate3 B = C` (inbound); `the_law3 C C = C` |
| `number-theory/padic_collapse.v` | `encode_padic_is_encode_relational_at_level0` | `the_law One One = Zero` gives bit 0, RHS asserts bit 1 |
| `category-topos/SelfReferentialTopos.v` | `map_is_endo`, `fwd_bwd_cancel`, `SELF_REFERENTIAL_TOPOS_ALGEBRA` | s=Map: LHS=C_I≠Map; neither disjunct holds |
| `category-topos/triadic_predicate_algebra.v` | `join_meet_absorption`, `meet_join_absorption` | counterexamples a=N,b=I and a=I,b=N |
| `geometry-metric/metricpole.v` | `equator_is_attractor` + 3 dependents | `field_op I_s N_s = N_s` ⇒ `tensor_step I_s = I_s` false |
| `geometry-metric/triadic_euclidean_geometry.v` | `tdist_sym` | `(a−b)²=(b−a)²` not derivable from the file's R axioms |
| `geometry-metric/triadic_geometry.v` | `A1_self_identity` | `op Inverse Inverse = Identity ≠ Inverse` |
| `geometry-metric/SDF.v` | `different_content_different_hash` | statement omits the children-equality hypothesis |
| `03-symbol-triangle/DualPrism.v` | `fano_map_involution` + 4 | `xb` xor only behaves on bits; spurious survivors over `nat` |
| `03-symbol-triangle/fanoplanetriadic.v` | `fano_line_Map_I_out_N_in` | correct third collinear point is F_in, not N_in |
| `03-symbol-triangle/triadic_natural_numbers.v` | `F_is_top`, `tLe_not_total` | `tLe` is actually total; degenerates to `mag a ≤ 0` |
| `03-symbol-triangle/triadic_predicate_logic.v` | `triadic_modus_ponens` | p=Identity,q=Infinity ⇒ Infinity ≠ p |
| `03-symbol-triangle/triadic_rational_numbers.v` | `triadic_has_omega_divisors` | `phase_mul` yields F only from an F input |
| `03-symbol-triangle/triadic_set_theory.v` | `no_empty_set`, `omega_in_every_powerset`, `global_ac_fails` | constant choice fn satisfies AC's 3rd conjunct, etc. |
| `04-symbol-square/triadic_complex_numbers.v` | `omega_is_universal_root`, `classical_plane_imaginary`, `tc_conj_dual_involutive` | unit mismatch; abstract R has no involution axiom |
| `04-symbol-square/InfinityThroughApex.v` | `apex_transform_involution`, `combined_always_xor_diag` | `xb (xb x 1) 1 = x` only for x∈{0,1} |
| `ai-ml/iso_computer.v` | `P_equals_NP`, `total_complexity_polynomial`, `iso_computer_turing_complete` | illegal Prop→Set elim; value is 8192≠8704; placeholder solver |
| `ai-ml/encoder.v` | `h_encodes_sum` | reduces to `(p+q)/2 = p+q` |
| `ai-ml/ml_gap_filling.v` / `MachineLearning.v` | `gap_has_unique_midpoint`, `fill_does_not_increase_gaps` | midpoint not unique for wide gaps; count can increase |
| `ai-ml/SAT3Computer.v` | `feedback_converges`, `d_zero_permanent` | off-by-one bound; converged field independent of dist |
| `ai-ml/gradient_descent_loss0.v` | `grid_closed_under_update` | product lands on a finer grid than the witness |
| `physics/TriadicThreeBody.v` | `stable_cells_count`, `TRIADIC_THREE_BODY_MASTER` | actual `I_in` cell count is 4, not 2 |
| `05-higher-symbols/full_9sym_invariant.v` | `L5_missing_F_out` | `compose5` makes M absorb from both sides for every symbol |
| `05-higher-symbols/RecursiveResolutionTower.v` | `sqrt2_convergent_3` | `7·7 − 2·5·5 = 0` in `nat`, RHS is 1 |
| `biology/*` | ~22 lemmas | `the_law2`/`the_law3` are NOR / `(x+y+1)mod3`, not the claimed group laws; several unbounded/antisymmetry claims |
| `crypto/triadic_sha256_analysis.v` | `phantom_requires_mult_structure` | a non-homomorphism can still be 2-to-1 |

---

## Full inventory of newly-`Admitted` statements (auto-generated)

### `00-foundations/closed_info_system.v` — 1 new
- `kernel_is_generated`

### `00-foundations/collapse.v` — 1 new
- `collapse_breaks_oscillation`

### `00-foundations/foldcollapse.v` — 8 new
- `gap_close_step`
- `gap_one_closes_to_terminal`
- `helix_op_terminal_wraps`
- `generator_is_terminal_inverse`
- `generator_visits_all_positions`
- `fold_isomorphism`
- `helix_inv_correct`
- `master_fold_theorem`

### `00-foundations/mul_as_wit_comp.v` — 1 new
- `one_is_multiplicative_identity_left`

### `00-foundations/projective_genesis.v` — 3 new
- `pi_as_limit`
- `pi_is_unique_closure`
- `alternating_remainder_sin`

### `00-foundations/set_witnessing.v` — 1 new
- `pow2_exp2_mod3`

### `00-foundations/witness_transp_eval.v` — 1 new
- `witness_transparent_ungameable`

### `02-symbol-line/encoding_any_sym_same_same.v` — 2 new
- `same_encodes_to_halfstep`
- `swap_preserves_encoding`

### `03-symbol-triangle/DualPrism.v` — 5 new
- `fano_map_involution`
- `map_fixed_only_Map`
- `dual_reads_codomain`
- `map_unique_agreement`
- `other_side_of_prism`

### `03-symbol-triangle/fanoplanetriadic.v` — 1 new
- `fano_line_Map_I_out_N_in`

### `03-symbol-triangle/triadic_natural_numbers.v` — 2 new
- `F_is_top`
- `tLe_not_total`

### `03-symbol-triangle/triadic_predicate_logic.v` — 1 new
- `triadic_modus_ponens`

### `03-symbol-triangle/triadic_rational_numbers.v` — 1 new
- `triadic_has_omega_divisors`

### `03-symbol-triangle/triadic_set_theory.v` — 3 new
- `no_empty_set`
- `omega_in_every_powerset`
- `global_ac_fails`

### `03-symbol-triangle/triadic_third_certificate.v` — 1 new
- `three_must_coexist`

### `04-symbol-square/InfinityThroughApex.v` — 2 new
- `apex_transform_involution`
- `combined_always_xor_diag`

### `04-symbol-square/diagonal_comparator.v` — 2 new
- `fixed_iff_diag`
- `off_diag_moves`

### `04-symbol-square/triadic_complex_numbers.v` — 3 new
- `tc_conj_dual_involutive`
- `omega_is_universal_root`
- `classical_plane_imaginary`

### `05-higher-symbols/full_9sym_invariant.v` — 1 new
- `L5_missing_F_out`

### `06-synthesis/GeneratorAttractor.v` — 3 new
- `attractor_walk_N_resolves`
- `attractor_walk_I_stable`
- `master_convergence`

### `06-synthesis/Unified.v` — 3 new
- `solved_iff_identity`
- `Millennium_Problems_Unified`
- `Millennium_Self_Proves`

### `06-synthesis/samesamebutdifferent.v` — 1 new
- `swap_preserves_law`

### `ai-ml/MachineLearning.v` — 1 new
- `fill_does_not_increase_gaps`

### `ai-ml/SAT3Computer.v` — 2 new
- `feedback_converges`
- `d_zero_permanent`

### `ai-ml/Transformer.v` — 2 new
- `T5_wall_theorem`
- `transformer_other_side`

### `ai-ml/encoder.v` — 1 new
- `h_encodes_sum`

### `ai-ml/gen_lang_model.v` — 1 new
- `standard_lm_cannot_close_gap`

### `ai-ml/gradient_descent_loss0.v` — 1 new
- `grid_closed_under_update`

### `ai-ml/iso_computer.v` — 3 new
- `iso_computer_turing_complete`
- `total_complexity_polynomial`
- `P_equals_NP`

### `ai-ml/learning_symbol_mapping.v` — 1 new
- `learned_consistent_with_sym2`

### `ai-ml/ml_gap_filling.v` — 1 new
- `gap_has_unique_midpoint`

### `arc-agi/ColorGauge.v` — 1 new
- `gauge_action_compose`

### `biology/HelixArithClosed.v` — 5 new
- `twos_comp_self_is_zero`
- `helix_geq_carry_correct`
- `helix_full_subtractor_correct`
- `borrow_is_negb_carry`
- `div_loop_correct`

### `biology/HelixHigherOrder.v` — 2 new
- `horner_at_2_mod3`
- `helix_filters_accept_one_third`

### `biology/ProteinPrime.v` — 1 new
- `crt_condition_implies_stable`

### `biology/bio_dirac_proofs.v` — 7 new
- `commutator_jacobi`
- `spectral_gap_nonneg`
- `risk_le_one`
- `disc_separation_antisym`
- `dominant_row_positive_center`
- `high_hydrophobicity_implies_ordered`
- `gap_monotone_in_hydrophobicity`

### `biology/double_helix.v` — 7 new
- `law2_assoc`
- `law2_identity`
- `law2_self_inverse`
- `law3_identity`
- `operator_strand_period2`
- `helix_pos_mod6`
- `crt_operator_recovery`

### `category-topos/SelfReferentialTopos.v` — 3 new
- `map_is_endo`
- `fwd_bwd_cancel`
- `SELF_REFERENTIAL_TOPOS_ALGEBRA`

### `category-topos/triadic_predicate_algebra.v` — 2 new
- `join_meet_absorption`
- `meet_join_absorption`

### `complexity-sat/ThreeSAT_InverseConstruction.v` — 2 new
- `construct_satisfies_first_lit`
- `score_permutation_same`

### `complexity-sat/ThreeSAT_complete.v` — 2 new
- `compose_id_left`
- `compose_id_right`

### `complexity-sat/TriadicComplexity.v` — 3 new
- `op_native_cost_is_constant`
- `algo_A_is_I_phase`
- `algo_B_is_N_phase`

### `complexity-sat/geometric_complexity.v` — 3 new
- `base_factor_large_lt_half`
- `geom_decay`
- `geometric_complexity_constant`

### `crypto/triadic_sha256_analysis.v` — 1 new
- `phantom_requires_mult_structure`

### `geometry-metric/SDF.v` — 1 new
- `different_content_different_hash`

### `geometry-metric/metricpole.v` — 4 new
- `equator_is_attractor`
- `tensor_determines_attractor`
- `complete_sphere_structure`
- `MetricPoleAttractorTheorem`

### `geometry-metric/triadic_euclidean_geometry.v` — 1 new
- `tdist_sym`

### `geometry-metric/triadic_geometry.v` — 1 new
- `A1_self_identity`

### `millennium-problems/NavierStokes.v` — 1 new
- `NS_no_blowup_from_sobolev`

### `millennium-problems/OctonionMillennium.v` — 1 new
- `oct_non_associative`

### `millennium-problems/triadic_riemannian_geometry.v` — 3 new
- `i_metric_i_phase`
- `n_metric_i_phase`
- `cross_layer_via_omega`

### `number-systems/BigIntArith.v` — 2 new
- `sub_bits_via_twos_complement`
- `sub_uses_n_strand`

### `number-systems/MetricInvariantRings.v` — 1 new
- `cyclic_dist_rotation_invariant`

### `number-systems/set_field_closure.v` — 4 new
- `pow2_exp2_mod3`
- `fermat_maps_to_diagonal`
- `fermat_is_unit`
- `fermat_permanently_diagonal`

### `number-systems/tdfloat_ieee_resolution.v` — 2 new
- `ieee_add_not_associative`
- `one_tenth_not_dyadic`

### `number-theory/GaussianPrimesCorollary.v` — 2 new
- `brahmagupta_fibonacci`
- `norm_multiplicative`

### `number-theory/directed_adic.v` — 2 new
- `rotate3_is_outbound_step`
- `law3_to_C_means_converging`

### `number-theory/padic_collapse.v` — 1 new
- `encode_padic_is_encode_relational_at_level0`

### `packages/DIM/dim_arith.v` — 1 new
- `arith_mode_binding`

### `packages/DIM/dim_cas_compute.v` — 2 new
- `operation_sign_valid`
- `minimal_binding_sufficiency`

### `packages/DIM/dim_consensus.v` — 3 new
- `receipt_data_binding`
- `equivocation_evidence_sound`
- `quorum_cert_is_threshold`

### `packages/DIM/dim_reproducibility.v` — 1 new
- `prob_receipt_binding`

### `packages/DIM/dim_training.v` — 1 new
- `training_receipt_binding`

### `physics/TriadicThreeBody.v` — 2 new
- `stable_cells_count`
- `TRIADIC_THREE_BODY_MASTER`


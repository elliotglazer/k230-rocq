(** Exact arbitrary-code alignment of the trace's matrix with the first
    emitted-closure matrix. This uses internal substitution composition. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SourceBounded SourceFixedSwap SourceFiniteCutoffShift
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  SourceSubstitutionComposition RenamingSubstitution SchemaRenamingDescriptors
  SubstitutionSource SourceUpperTraceRecipe SourceNativeKMatrixMaps.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_cutoff_shift_map_tail M depth b c n i :
  source_cutoff_shift_map M depth b c n ->
  substitution_lookup M b c n (code_numeral M (S depth))
    (source_succ_iter M depth i) (source_succ_iter M depth (succM M i)).
Proof.
  revert b c n. induction depth as [|d IH];intros b c n HM.
  - destruct HM as [-> [-> ->]]. apply source_cutoff_shift_base_lookup.
  - destruct HM as [u [v [m [HM HL]]]]. cbn [source_succ_iter].
    apply (proj2 (substitution_lift_tail M u v m (code_numeral M (S d)) b c n
      (source_succ_iter M d i) (source_succ_iter M d (succM M i)) HL)).
    exact (IH u v m HM).
Qed.

Lemma source_swap_delta_prefix M delta :
  renaming_lookup M (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) delta
    (zeroM M) (code_numeral M 1) /\
  renaming_lookup M (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) delta
    (code_numeral M 1) (zeroM M).
Proof.
  split.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1)))).
    apply (descriptor_beta_certificate M 3 1 0 1 1);reflexivity||lia.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 1)))).
    apply (descriptor_beta_certificate M 3 1 1 0 1);reflexivity||lia.
Qed.

Lemma source_two_succ_not_lt_two M i :
  ~coding_lt M (succM M (succM M i)) (code_numeral M 2).
Proof.
  intro H. exact (coding_not_lt_zero M i
    (proj1 (coding_lt_succ_cancel M i (zeroM M))
      (proj1 (coding_lt_succ_cancel M (succM M i) (code_numeral M 1)) H))).
Qed.

Theorem source_swapped_cutoff_two_increment M phi f g delta k :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) delta f -> source_cutoff_shift M 2 f g ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (succM M delta) g.
Proof.
  intros HP HR [b [c [n [HM HG]]]].
  apply (proj2 (numerical_renaming_substitution M phi (code_numeral M 3)
    (code_numeral M 1) (code_numeral M 2) (succM M delta) g)).
  apply (numerical_substitution_composition M phi k
    (code_numeral M 3) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) delta) b c n (code_numeral M 3)
    (code_numeral M 3) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) (succM M delta)) f g HP
    (proj1 (numerical_renaming_substitution M phi _ _ _ delta f) HR) HG).
  intros i j v _ HFirst HSecond.
  apply (proj2 (renaming_substitution_lookup M (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) delta i j)) in HFirst.
  apply (proj1 (renaming_substitution_lookup M (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (succM M delta) i v)).
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
      (proj1 (source_swap_delta_prefix M delta))) as E. subst j.
    pose proof (substitution_lookup_functional M b c n (code_numeral M 3)
      (code_numeral M 1) v (code_numeral M 1) HSecond
      (source_cutoff_shift_map_fixed_lookup M 2 b c n HM 1)) as E. subst v.
    exact (proj1 (source_swap_delta_prefix M (succM M delta))).
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
        (proj2 (source_swap_delta_prefix M delta))) as E. subst j.
      pose proof (substitution_lookup_functional M b c n (code_numeral M 3)
        (zeroM M) v (zeroM M) HSecond
        (source_cutoff_shift_map_fixed_lookup M 2 b c n HM 0)) as E. subst v.
      exact (proj2 (source_swap_delta_prefix M (succM M delta))).
    + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _
        (source_two_succ_not_lt_two M i''))) in HFirst.
      rewrite !Arithmetic.add_succ in HFirst. subst j.
      pose proof (source_cutoff_shift_map_tail M 2 b c n (addM M i'' delta) HM) as HTail.
      pose proof (substitution_lookup_functional M b c n (code_numeral M 3)
        _ v _ HSecond HTail) as E. subst v.
      apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))).
      cbn [source_succ_iter]. rewrite !Arithmetic.add_succ.
      rewrite (Arithmetic.add_comm M i'' (succM M delta)),Arithmetic.add_succ,
        (Arithmetic.add_comm M delta i''). reflexivity.
Qed.

Theorem source_trace_matrix_is_swap_delta_one M phi trace swapped shifted atom body k :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) swapped ->
  source_cutoff_shift M 2 swapped shifted ->
  sf_relation M SFMember (zeroM M) (code_numeral M 2) atom ->
  sf_relation M SFAnd atom shifted body -> sf_relation M SFEx body (zeroM M) trace ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M 1) shifted.
Proof.
  intros HP HR HS _ _ _.
  exact (source_swapped_cutoff_two_increment M phi swapped shifted (zeroM M) k HP HR HS).
Qed.

Theorem source_upper_trace_theta_matrix M phi trace theta k :
  source_bounded M phi k ->source_upper_trace M phi trace ->
  source_cutoff_shift M 1 trace theta ->
  exists atom matrix body,source_native_k_matrix M NativeKA phi matrix /\
    sf_relation M SFMember (zeroM M) (code_numeral M 3) atom /\
    sf_relation M SFAnd atom matrix body /\ sf_relation M SFEx body (zeroM M) theta.
Proof.
  intros HP [swapped [shifted [atom [body [HS [HT [HA [HB HE]]]]]]]]
    [b [c [n [HM HSub]]]].
  pose proof (source_swapped_cutoff_two_increment M phi swapped shifted (zeroM M) k
    HP HS HT) as HFirst.
  destruct (proj1 (numerical_substitution_quantifier M false body trace b c n
    (code_numeral M 2) theta HE) HSub) as [d [e [l [inner [HL [HInner HTheta]]]]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd atom shifted body d e l
    (code_numeral M 3) inner (or_introl eq_refl) HB) HInner)
    as [atom' [matrix [HAtom [HMatrix HBody]]]].
  assert (HMap2:source_cutoff_shift_map M 2 d e l).
  { exists b,c,n. auto. }
  assert (HSecond:source_native_k_matrix M NativeKA phi matrix).
  { exact (source_swapped_cutoff_two_increment M phi shifted matrix (code_numeral M 1)
      k HP HFirst ltac:(exists d,e,l;auto)). }
  destruct (proj1 (numerical_substitution_member M (zeroM M) (code_numeral M 2)
    atom d e l (code_numeral M 3) atom' HA) HAtom)
    as [u [v [HU [HV HAtom']]]].
  apply (proj1 (substitution_lift_head M b c n (code_numeral M 2) d e l u HL)) in HU.
  subst u.
  assert (HV3:substitution_lookup M d e l (code_numeral M 3)
    (code_numeral M 2) (code_numeral M 3)).
  { exact (source_cutoff_shift_map_tail M 2 d e l (zeroM M) HMap2). }
  pose proof (substitution_lookup_functional M d e l (code_numeral M 3)
    (code_numeral M 2) v (code_numeral M 3) HV HV3) as E. subst v.
  exists atom',matrix,inner. auto.
Qed.

Print Assumptions source_cutoff_shift_map_tail.
Print Assumptions source_swapped_cutoff_two_increment.
Print Assumptions source_trace_matrix_is_swap_delta_one.
Print Assumptions source_upper_trace_theta_matrix.

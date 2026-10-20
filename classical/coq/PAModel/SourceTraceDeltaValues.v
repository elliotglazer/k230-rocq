(** Matrix alignment with a model-valued parameter tail. Source binders
    increment this tail; they need not preserve the canonical role names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded NumericalRenaming NumericalRenamingMaps
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource
  SourceSubstitutionComposition SourceRoleReopening SourceDoubleSpecialization
  SourceTraceMatrixAlignment SourceTraceValueAlignment SourceRenamingBounds
  SourceRenamingWellformedness RenamingSubstitution.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition source_trace_value_syntax M theta x p value := exists some inner pair pb,
  numerical_instantiation M theta x some /\ sf_relation M SFEx inner (zeroM M) some /\
  numerical_instantiation M inner p pair /\ sf_relation M SFAnd pb value pair.

Theorem source_swapped_matrix_reopening M phi matrix value k delta x p ab ac rb rc :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) delta matrix ->
  source_role_reopening M x p ab ac ->source_role_reopening M p x rb rc ->
  numerical_substitution M matrix ab ac (code_numeral M 2) (zeroM M) value ->
  numerical_substitution M phi rb rc (code_numeral M 2) delta value.
Proof.
  intros HP HA [HP0 HX1] [HX0 HP1] HV.
  apply (numerical_substitution_composition M phi k
    (code_numeral M 3) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) delta)
    ab ac (code_numeral M 2) (zeroM M) rb rc (code_numeral M 2)
    delta matrix value HP
    (proj1 (numerical_renaming_substitution M phi _ _ _ _ matrix) HA) HV).
  intros i j v _ HFirst HSecond.
  apply (proj2 (renaming_substitution_lookup M (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) delta i j)) in HFirst.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
      (proj1 (source_swap_delta_prefix M delta))) as E. subst j.
    pose proof (substitution_lookup_functional M ab ac (code_numeral M 2) (zeroM M)
      (code_numeral M 1) v x HSecond HX1) as E. subst v.
    exact (source_two_prefix_change_base M rb rc (zeroM M) x delta
      (coding_zero_lt_succ M (code_numeral M 1)) HX0).
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
        (proj2 (source_swap_delta_prefix M delta))) as E. subst j.
      pose proof (substitution_lookup_functional M ab ac (code_numeral M 2) (zeroM M)
        (zeroM M) v p HSecond HP0) as E. subst v.
      exact (source_two_prefix_change_base M rb rc (code_numeral M 1) p delta
        (coding_lt_succ M (code_numeral M 1)) HP1).
    + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _
        (source_two_succ_not_lt_two M i''))) in HFirst.
      rewrite !Arithmetic.add_succ in HFirst. subst j.
      pose proof (substitution_lookup_functional M ab ac (code_numeral M 2) (zeroM M)
        _ v _ HSecond (source_role_reopening_tail M ab ac (addM M i'' delta))) as E.
      subst v. right. split;[exact (source_two_succ_not_lt_two M i'')|].
      exists i''. split.
      * cbn [code_numeral]. now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
      * apply Arithmetic.add_comm.
Qed.

Theorem source_trace_delta_value_alignment M phi theta atom matrix body x p value k delta rb rc :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) delta matrix ->
  sf_relation M SFAnd atom matrix body -> sf_relation M SFEx body (zeroM M) theta ->
  source_trace_value_syntax M theta x p value ->source_role_reopening M p x rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2) delta value.
Proof.
  intros HP HA HBody HTheta [some [inner [pair [pb [HSome [HEx [HValue HPair]]]]]]] HTarget.
  destruct HSome as [sb [sc [HX HSome]]].
  destruct (proj1 (numerical_substitution_quantifier M false body theta sb sc
    (code_numeral M 1) (zeroM M) some HTheta) HSome)
    as [ad [ae [am [inner' [HL [HInner HSomeEx]]]]]].
  pose proof (proj1 (proj2 (sf_relation_injective M SFEx SFEx inner' (zeroM M)
    inner (zeroM M) some HSomeEx HEx))) as E. subst inner'.
  destruct (proj1 (numerical_substitution_binary M SFAnd atom matrix body ad ae am
    (code_numeral M 1) inner (or_introl eq_refl) HBody) HInner)
    as [atom' [matrix' [HAtom' [HMatrix' HInnerAnd]]]].
  destruct HValue as [tb [tc [HPVal HValue]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd atom' matrix' inner tb tc
    (code_numeral M 1) (zeroM M) pair (or_introl eq_refl) HInnerAnd) HValue)
    as [pb' [value' [HPb' [HValue' HPair']]]].
  pose proof (proj2 (proj2 (sf_relation_injective M SFAnd SFAnd pb' value' pb value
    pair HPair' HPair))) as E. change (value'=value) in E. subst value'.
  destruct (source_role_reopening_total M x p) as [ab [ac HReopen]].
  destruct (source_renaming_range_bound M (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) delta k) as [l HRange].
  pose proof (numerical_renaming_preserves_bound M phi _ _ _ _ matrix k l HP HA HRange) as HM.
  assert (HV:numerical_substitution M matrix ab ac (code_numeral M 2) (zeroM M) value).
  { apply (numerical_substitution_composition M matrix l ad ae am (code_numeral M 1)
      tb tc (code_numeral M 1) (zeroM M) ab ac (code_numeral M 2) (zeroM M)
      matrix' value HM HMatrix' HValue').
    exact (source_double_specialization_maps M x p sb sc ad ae am tb tc ab ac
      l HX HL HPVal HReopen). }
  exact (source_swapped_matrix_reopening M phi matrix value k delta x p ab ac rb rc
    HP HA HReopen HTarget HV).
Qed.

Print Assumptions source_swapped_matrix_reopening.
Print Assumptions source_trace_delta_value_alignment.

(** The trace value is the genuine simultaneous substitution
    phi[x,p,parameters], for arbitrary internal phi. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded SourceFiniteCutoffShift
  SourceUpperTraceRecipe SourceUpperTraceValues SourceTraceMatrixAlignment
  SourceNativeKMatrixMaps NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceSubstitutionComposition SourceRoleReopening SourceDoubleSpecialization
  RenamingSubstitution SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_two_prefix_change_base M rb rc i v base :
  coding_lt M i (code_numeral M 2) ->
  substitution_lookup M rb rc (code_numeral M 2) (zeroM M) i v ->
  substitution_lookup M rb rc (code_numeral M 2) base i v.
Proof.
  intros HI HS.
  apply (proj2 (substitution_lookup_inside M rb rc (code_numeral M 2) base i v HI)).
  exact (proj1 (substitution_lookup_inside M rb rc (code_numeral M 2) (zeroM M) i v HI) HS).
Qed.

Theorem source_native_A_reopening M phi matrix value count x p ab ac rb rc :
  source_bounded M phi (succM M (succM M count)) ->
  source_native_k_matrix M NativeKA phi matrix ->
  source_role_reopening M x p ab ac ->source_role_reopening M p x rb rc ->
  numerical_substitution M matrix ab ac (code_numeral M 2) (zeroM M) value ->
  numerical_substitution M phi rb rc (code_numeral M 2) (code_numeral M 2) value.
Proof.
  intros HP HA [HP0 HX1] [HX0 HP1] HV.
  apply (numerical_substitution_composition M phi (succM M (succM M count))
    (code_numeral M 3) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) (code_numeral M 2))
    ab ac (code_numeral M 2) (zeroM M) rb rc (code_numeral M 2)
    (code_numeral M 2) matrix value HP
    (proj1 (numerical_renaming_substitution M phi _ _ _ _ matrix) HA) HV).
  intros i j v _ HFirst HSecond.
  apply (proj2 (renaming_substitution_lookup M (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M 2) i j)) in HFirst.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
      (native_k_lookup_first M NativeKA)) as E. subst j.
    pose proof (substitution_lookup_functional M ab ac (code_numeral M 2) (zeroM M)
      (code_numeral M 1) v x HSecond HX1) as E. subst v.
    exact (source_two_prefix_change_base M rb rc (zeroM M) x (code_numeral M 2)
      (coding_zero_lt_succ M (code_numeral M 1)) HX0).
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
        (native_k_lookup_second M NativeKA)) as E. subst j.
      pose proof (substitution_lookup_functional M ab ac (code_numeral M 2) (zeroM M)
        (zeroM M) v p HSecond HP0) as E. subst v.
      exact (source_two_prefix_change_base M rb rc (code_numeral M 1) p (code_numeral M 2)
        (coding_lt_succ M (code_numeral M 1)) HP1).
    + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _
        (source_two_succ_not_lt_two M i''))) in HFirst.
      repeat rewrite Arithmetic.add_succ in HFirst.
      rewrite (Arithmetic.add_comm M i'' (code_numeral M 2)) in HFirst.
      cbn [code_numeral] in HFirst.
      repeat rewrite Arithmetic.add_succ in HFirst.
      rewrite Arithmetic.add_zero in HFirst. subst j.
      pose proof (substitution_lookup_functional M ab ac (code_numeral M 2) (zeroM M)
        _ v _ HSecond (source_role_reopening_tail M ab ac (succM M (succM M i'')))) as E.
      subst v. right. split;[exact (source_two_succ_not_lt_two M i'')|].
      exists i''. split;[|].
      * cbn [code_numeral]. now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
      * cbn [code_numeral]. now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_trace_value_is_direct_substitution M phi trace theta x p value count rb rc :
  source_bounded M phi (succM M (succM M count)) ->
  source_upper_trace M phi trace -> source_cutoff_shift M 1 trace theta ->
  source_trace_theta_value M theta x p value ->source_role_reopening M p x rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2) (code_numeral M 2) value.
Proof.
  intros HP HT HS [some [inner [pair [pb [HSome [HEx [HValue [HPb HPair]]]]]]]] HTarget.
  destruct (source_upper_trace_theta_matrix M phi trace theta (succM M (succM M count)) HP HT HS)
    as [atom [matrix [body [HA [HAtom [HBody HTheta]]]]]].
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
  assert (HV:numerical_substitution M matrix ab ac (code_numeral M 2) (zeroM M) value).
  { apply (numerical_substitution_composition M matrix
      (source_succ_iter M 4 count) ad ae am (code_numeral M 1)
      tb tc (code_numeral M 1) (zeroM M) ab ac (code_numeral M 2) (zeroM M)
      matrix' value (source_native_k_matrix_bound M NativeKA phi matrix count HP HA) HMatrix' HValue').
    exact (source_double_specialization_maps M x p sb sc ad ae am tb tc ab ac
      (source_succ_iter M 4 count) HX HL HPVal HReopen). }
  exact (source_native_A_reopening M phi matrix value count x p ab ac rb rc HP HA HReopen HTarget HV).
Qed.

Print Assumptions source_native_A_reopening.
Print Assumptions source_trace_value_is_direct_substitution.

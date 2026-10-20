(** Insert one unused parameter after the two predicate roles. The native
    matrices acquire the identical parameter-tail shift. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SourceBounded SourceNativeKMatrixMaps SourceFiniteCutoffShift
  SourceTraceMatrixAlignment SourceSubstitutionComposition NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma native_k_prefix_at_delta M s delta :
  renaming_lookup M (code_numeral M (native_k_dividend s))(code_numeral M 1)
    (code_numeral M 2) delta (zeroM M)(code_numeral M (native_k_first s)) /\
  renaming_lookup M (code_numeral M (native_k_dividend s))(code_numeral M 1)
    (code_numeral M 2) delta (code_numeral M 1)(code_numeral M (native_k_second s)).
Proof.
  split.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1)))).
    destruct s;cbn [native_k_dividend native_k_first].
    + apply (descriptor_beta_certificate M 3 1 0 1 1);reflexivity||lia.
    + apply (descriptor_beta_certificate M 4 1 0 0 2);reflexivity||lia.
    + apply (descriptor_beta_certificate M 2 1 0 0 1);reflexivity||lia.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 1)))).
    destruct s;cbn [native_k_dividend native_k_second].
    + apply (descriptor_beta_certificate M 3 1 1 0 1);reflexivity||lia.
    + apply (descriptor_beta_certificate M 4 1 1 1 1);reflexivity||lia.
    + apply (descriptor_beta_certificate M 2 1 1 2 0);reflexivity||lia.
Qed.

Theorem source_native_matrix_insert_input M s phi shifted matrix k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi shifted ->
  source_native_k_matrix M s shifted matrix ->
  numerical_renaming M phi (code_numeral M (native_k_dividend s))(code_numeral M 1)
    (code_numeral M 2)(succM M (code_numeral M (native_k_delta s))) matrix.
Proof.
  intros HP [b [c [n [HC HS]]]] HM.
  apply (proj2 (numerical_renaming_substitution M phi _ _ _ _ matrix)).
  apply (numerical_substitution_composition M phi k b c n (code_numeral M 3)
    (code_numeral M (native_k_dividend s))(code_numeral M 1)(code_numeral M 2)
    (addM M (code_numeral M 2)(code_numeral M (native_k_delta s)))
    (code_numeral M (native_k_dividend s))(code_numeral M 1)(code_numeral M 2)
    (addM M (code_numeral M 2)(succM M (code_numeral M (native_k_delta s))))
    shifted matrix HP HS (proj1 (numerical_renaming_substitution M shifted _ _ _ _ matrix) HM)).
  intros i j v _ HF HG.
  apply (proj1 (renaming_substitution_lookup M _ _ _ _ i v)).
  apply (proj2 (renaming_substitution_lookup M _ _ _ _ j v)) in HG.
  destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (substitution_lookup_functional M b c n (code_numeral M 3)(zeroM M) j
      (zeroM M) HF (source_cutoff_shift_map_fixed_lookup M 2 b c n HC 0)) as E. subst j.
    pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HG (native_k_lookup_first M s)) as E. subst v.
    exact (proj1 (native_k_prefix_at_delta M s (succM M (code_numeral M (native_k_delta s))))).
  - destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (substitution_lookup_functional M b c n (code_numeral M 3)(code_numeral M 1) j
        (code_numeral M 1) HF (source_cutoff_shift_map_fixed_lookup M 2 b c n HC 1)) as E. subst j.
      pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HG (native_k_lookup_second M s)) as E. subst v.
      exact (proj2 (native_k_prefix_at_delta M s (succM M (code_numeral M (native_k_delta s))))).
    + pose proof (substitution_lookup_functional M b c n (code_numeral M 3) _ j
        (succM M (succM M (succM M i''))) HF (source_cutoff_shift_map_tail M 2 b c n i'' HC)) as E.
      subst j. apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _
        (source_two_succ_not_lt_two M (succM M i'')))) in HG. subst v.
      apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))).
      rewrite !Arithmetic.add_succ. rewrite (Arithmetic.add_comm M i'' (succM M (code_numeral M (native_k_delta s)))),
        Arithmetic.add_succ,(Arithmetic.add_comm M (code_numeral M (native_k_delta s)) i''). reflexivity.
Qed.

Definition native_k_parameter_cutoff s := match s with NativeKA=>3|NativeKB=>5|NativeKC=>6 end.

Theorem source_native_matrix_insert_output M s phi matrix shifted k :
  source_bounded M phi k ->source_native_k_matrix M s phi matrix ->
  source_cutoff_shift M (native_k_parameter_cutoff s) matrix shifted ->
  numerical_renaming M phi (code_numeral M (native_k_dividend s))(code_numeral M 1)
    (code_numeral M 2)(succM M (code_numeral M (native_k_delta s))) shifted.
Proof.
  intros HP HM [b [c [n [HC HS]]]].
  apply (proj2 (numerical_renaming_substitution M phi _ _ _ _ shifted)).
  apply (numerical_substitution_composition M phi k
    (code_numeral M (native_k_dividend s))(code_numeral M 1)(code_numeral M 2)
    (addM M (code_numeral M 2)(code_numeral M (native_k_delta s)))
    b c n (code_numeral M (S(native_k_parameter_cutoff s)))
    (code_numeral M (native_k_dividend s))(code_numeral M 1)(code_numeral M 2)
    (addM M (code_numeral M 2)(succM M (code_numeral M (native_k_delta s))))
    matrix shifted HP (proj1 (numerical_renaming_substitution M phi _ _ _ _ matrix) HM) HS).
  intros i j v _ HF HG.
  apply (proj2 (renaming_substitution_lookup M _ _ _ _ i j)) in HF.
  apply (proj1 (renaming_substitution_lookup M _ _ _ _ i v)).
  destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HF (native_k_lookup_first M s)) as E. subst j.
    assert (HFix:substitution_lookup M b c n (code_numeral M (S(native_k_parameter_cutoff s)))
      (code_numeral M (native_k_first s))(code_numeral M (native_k_first s))).
    { pose proof (source_cutoff_shift_map_fixed_lookup M (native_k_parameter_cutoff s) b c n HC (native_k_first s)) as H.
      destruct s;exact H. }
    pose proof (substitution_lookup_functional M _ _ _ _ _ v _ HG HFix) as E. subst v.
    exact (proj1 (native_k_prefix_at_delta M s (succM M (code_numeral M (native_k_delta s))))).
  - destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HF (native_k_lookup_second M s)) as E. subst j.
      assert (HFix:substitution_lookup M b c n (code_numeral M (S(native_k_parameter_cutoff s)))
        (code_numeral M (native_k_second s))(code_numeral M (native_k_second s))).
      { pose proof (source_cutoff_shift_map_fixed_lookup M (native_k_parameter_cutoff s) b c n HC (native_k_second s)) as H.
        destruct s;exact H. }
      pose proof (substitution_lookup_functional M _ _ _ _ _ v _ HG HFix) as E. subst v.
      exact (proj2 (native_k_prefix_at_delta M s (succM M (code_numeral M (native_k_delta s))))).
    + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))) in HF. subst j.
      assert (HTail:substitution_lookup M b c n (code_numeral M (S(native_k_parameter_cutoff s)))
        (addM M (succM M (succM M i''))(code_numeral M (native_k_delta s)))
        (addM M (succM M (succM M i''))(succM M (code_numeral M (native_k_delta s))))).
      { pose proof (source_cutoff_shift_map_tail M (native_k_parameter_cutoff s) b c n (succM M i'') HC) as H.
        destruct s;cbn [native_k_delta native_k_parameter_cutoff source_succ_iter code_numeral] in *;
          rewrite !Arithmetic.add_succ;
          repeat rewrite (Arithmetic.add_comm M i'');
          rewrite !Arithmetic.add_succ,Arithmetic.add_zero;exact H. }
      pose proof (substitution_lookup_functional M _ _ _ _ _ v _ HG HTail) as E. subst v.
      apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))). reflexivity.
Qed.

Print Assumptions source_native_matrix_insert_input.
Print Assumptions source_native_matrix_insert_output.

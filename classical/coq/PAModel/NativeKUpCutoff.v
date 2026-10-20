(** The literal beta[0] up-shift map is already an actual one-binder
    cutoff-shift map; no fresh map or extensional encoding is needed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming
  RenamingSubstitution SourceFiniteCutoffShift SourceNativeKShifts SchemaRenamingDescriptors.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma native_k_upshift_base M :
  addM M (code_numeral M 1) (code_numeral M 1)=code_numeral M 2.
Proof. change (addM M (succM M (zeroM M)) (succM M (zeroM M))=succM M (succM M (zeroM M))).
  now rewrite Arithmetic.add_succ,Arithmetic.add_zero. Qed.

Theorem native_k_upshift_cutoff_map M :
  source_cutoff_shift_map M 1 (zeroM M)(zeroM M)(code_numeral M 1).
Proof.
  exists (zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
  split;[reflexivity|]. split.
  - apply (proj2 (substitution_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (zeroM M)))).
    apply (descriptor_beta_certificate M 0 0 0 0 0);reflexivity||lia.
  - intros i v HV.
    pose proof (substitution_lookup_functional M _ _ _ _ i v (succM M i) HV
      (source_cutoff_shift_base_lookup M i)) as E. subst v.
    right. split.
    + intro H. exact (coding_not_lt_zero M i (proj1 (coding_lt_succ_cancel M i (zeroM M)) H)).
    + exists i. split.
      * change (succM M i=addM M (succM M (zeroM M)) i).
        now rewrite Arithmetic.add_succ,Arithmetic.add_zero.
      * change (succM M (succM M i)=addM M (succM M (succM M (zeroM M))) i).
        now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem native_k_upshift_substitution M f g :source_native_k_upshift M f g ->
  numerical_substitution M f (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 2) g.
Proof.
  intro H. apply (proj1 (numerical_renaming_substitution M f _ _ _ _ g)) in H.
  now rewrite native_k_upshift_base in H.
Qed.

Print Assumptions native_k_upshift_cutoff_map.

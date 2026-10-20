(** The root matrix uses the actual reopening prefix [b,a]. Its private
    container name c is outside the original matrix's free-index bound. *)
From Stdlib Require Import List.
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalContexts NumericalContextRenaming NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceBounded SourceRoleAbstraction SourceRoleReopening SourceQuantifierRules
  SourceImplicationAllShift SourceRenamingIdentity SourceShiftSpecialization
  SourceFourMapComparison SourceNamedScopes SourceNamedScopeBinding SourceFiniteMapLifts
  NativeCoreLeafAlignment.
From FOL.Tennenbaum Require Import Peano.
Import ListNotations.
Unset Implicit Arguments.

Theorem native_core_root_alignment M a b c phi abstract shifted out arb arc sb sc db dc dn :
  source_bounded M phi c ->source_role_map M a b arb arc ->
  numerical_renaming M phi arb arc (source_role_length M a b) (code_numeral M 2) abstract ->
  source_formula_shift M abstract shifted ->source_role_reopening M a b sb sc ->
  source_substitution_lifts M 1 sb sc (code_numeral M 2) (zeroM M) db dc dn ->
  numerical_substitution M shifted db dc dn (code_numeral M 1) out ->
  named_scope_renaming M [c] phi out.
Proof.
  intros HB HM HR HS HOpen HL HOut.
  pose proof (source_role_abstraction_bounded M a b phi abstract c HB
    (ex_intro _ arb (ex_intro _ arc (conj HM HR)))) as HAB.
  pose proof (source_shift_bound M abstract shifted _ HAB HS) as HShiftBound.
  assert (HId:numerical_substitution M shifted (zeroM M)(zeroM M)(zeroM M)(zeroM M) shifted).
  { apply (proj1 (numerical_renaming_empty_substitution M shifted _ _ _ shifted)).
    apply (numerical_renaming_identity_on_bound M shifted _ _ _ _ _ HShiftBound).
    intros i _. apply source_empty_renaming_lookup. }
  destruct (named_scope_map_total M [c]) as (tb&tc&HT).
  exists tb,tc. split;[exact HT|].
  apply (proj2 (numerical_renaming_substitution M phi tb tc (named_scope_bound M [c]) (code_numeral M 1) out)).
  apply (numerical_two_renamings_two_substitutions_compare M phi c
    arb arc (source_role_length M a b) (code_numeral M 2)
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) db dc dn (code_numeral M 1)
    tb tc (named_scope_bound M [c]) (addM M (named_scope_bound M [c]) (code_numeral M 1))
    abstract shifted shifted out HB HR HS HId HOut).
  intros i j1 j2 j3 v HI HRole HShift HIdentity HLast.
  apply context_shift_lookup in HShift. subst j2.
  pose proof (substitution_lookup_functional M _ _ _ _ _ j3 _ HIdentity
    (source_empty_substitution_lookup M (succM M j1))) as E3. subst j3.
  assert (HIc:i<>c).
  { exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i c HI). }
  assert (HV:v=succM M i).
  { apply HM in HRole. destruct HOpen as [HOutput HInput].
    destruct HRole as [[-> ->]|[_ [[-> ->]|[_ ->]]]].
    - pose proof (source_substitution_lifts_tail M 1 sb sc (code_numeral M 2) (zeroM M)
        db dc dn (zeroM M) b HL HOutput) as HLast'.
      exact (substitution_lookup_functional M _ _ _ _ _ v _ HLast HLast').
    - pose proof (source_substitution_lifts_tail M 1 sb sc (code_numeral M 2) (zeroM M)
        db dc dn (code_numeral M 1) a HL HInput) as HLast'.
      exact (substitution_lookup_functional M _ _ _ _ _ v _ HLast HLast').
    - pose proof (source_substitution_lifts_tail M 1 sb sc (code_numeral M 2) (zeroM M)
        db dc dn (succM M (succM M i)) i HL (source_role_reopening_tail M sb sc i)) as HLast'.
      exact (substitution_lookup_functional M _ _ _ _ _ v _ HLast HLast'). }
  subst v. apply (proj1 (renaming_substitution_lookup M tb tc _ _ i (succM M i))).
  apply HT. cbn [named_scope_index]. right. split;[exact HIc|]. exists i. auto.
Qed.

Print Assumptions native_core_root_alignment.

(** The literal least-ordinal witness really belongs to its Replacement
    range, and its ordinal/predicate payloads are actual source proofs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalRenaming NumericalRenamingMaps NumericalSubstitutionMaps
  NumericalSubstitution RenamingSubstitution NumericalInstantiation
  SourceRoleReopening SourceFixedSwap SourceDomainInstances SourceOrdinalPredicate
  SourceOrdinalCollectionRecipe SourceOrdinalCollectionMaps SchemaRenamingDescriptors
  SourceReplacementMemberAt NumericalSourceFull SourceConjunctionRules.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Lemma source_fixed_swap_reopening M :
  source_role_reopening M (zeroM M) (code_numeral M 1) (code_numeral M 3) (code_numeral M 1).
Proof.
  split.
  - apply (proj2 (substitution_lookup_inside M (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) (zeroM M) (code_numeral M 1)
      (coding_zero_lt_succ M (code_numeral M 1)))).
    exact (proj1 (renaming_lookup_inside M (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) (zeroM M) (code_numeral M 1)
      (coding_zero_lt_succ M (code_numeral M 1))) (proj1 (source_fixed_swap_map M))).
  - apply (proj2 (substitution_lookup_inside M (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) (code_numeral M 1) (zeroM M)
      (coding_lt_succ M (code_numeral M 1)))).
    exact (proj1 (renaming_lookup_inside M (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) (code_numeral M 1) (zeroM M)
      (coding_lt_succ M (code_numeral M 1))) (proj2 (source_fixed_swap_map M))).
Qed.

Theorem source_full_oc_witness_member M b c n phi oc matrix leastbody profile count s x input member :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  schema_renaming M RepC oc matrix ->
  numerical_renaming M oc (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) leastbody ->
  source_replacement_profile_at_graph M s x matrix profile ->
  sf_relation M SFMember (code_numeral M 1) x input ->sf_relation M SFMember (zeroM M) s member ->
  source_full_prv M b c n profile ->source_full_prv M b c n input ->
  source_full_prv M b c n leastbody ->source_full_prv M b c n member.
Proof.
  intros HB HOC HM HSwap HP HI HE PP PI PW.
  pose proof (source_oc_form_bounded M _ phi oc count (source_ordinal_predicate_bounded M) HB HOC) as HOB.
  pose proof (proj1 (numerical_renaming_substitution M oc (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) leastbody) HSwap) as HS.
  rewrite coding_add_zero_r in HS.
  exact (source_full_replacement_member_at M b c n oc matrix profile count s x (zeroM M)
    (code_numeral M 1) (code_numeral M 3) (code_numeral M 1) leastbody input member
    HOB HM HP (source_fixed_swap_reopening M) HS HI HE PP PI PW).
Qed.

Theorem source_oc_reopened_payload M phi oc leastbody k :
  source_bounded M phi k ->source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  numerical_renaming M oc (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) leastbody ->
  exists inner tail,sf_relation M SFAnd (source_ordinal_predicate_code M) phi inner /\
    sf_relation M SFAnd inner tail leastbody.
Proof.
  intros HB (ord&swapped&tail&inner&HO&HQ&HT&HI&HOC) HR.
  destruct (proj1 (numerical_renaming_binary M SFAnd inner tail oc _ _ _ _ leastbody
    (or_introl eq_refl) HOC) HR) as (inner'&tail'&RI&RT&HBody).
  destruct (proj1 (numerical_renaming_binary M SFAnd ord swapped inner _ _ _ _ inner'
    (or_introl eq_refl) HI) RI) as (ord'&phi'&RO&RP&HInner).
  pose proof (source_fixed_swap_twice M phi swapped phi' k HB HQ RP) as EP. subst phi'.
  pose proof (source_collection_domain_instance_renaming M (source_ordinal_predicate_code M)
    (code_numeral M 1) ord (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) ord' (zeroM M) (source_ordinal_predicate_bounded M)
    HO RO (proj2 (source_fixed_swap_map M))) as HOrd.
  pose proof (numerical_instantiation_functional M _ (zeroM M) ord' (source_ordinal_predicate_code M)
    HOrd (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))) as EO. subst ord'.
  exists inner',tail'. auto.
Qed.

Theorem source_full_oc_witness_payload M b c n phi oc leastbody k :
  source_bounded M phi k ->source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  numerical_renaming M oc (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) leastbody ->source_full_prv M b c n leastbody ->
  source_full_prv M b c n (source_ordinal_predicate_code M) /\source_full_prv M b c n phi.
Proof.
  intros HB HO HR PW.
  destruct (source_oc_reopened_payload M phi oc leastbody k HB HO HR) as (inner&tail&HI&HW).
  pose proof (source_full_conjunction_left M b c n inner tail leastbody HW PW) as PInner.
  split.
  - exact (source_full_conjunction_left M b c n _ phi inner HI PInner).
  - exact (source_full_conjunction_right M b c n _ phi inner HI PInner).
Qed.

Print Assumptions source_full_oc_witness_member.
Print Assumptions source_oc_reopened_payload.
Print Assumptions source_full_oc_witness_payload.

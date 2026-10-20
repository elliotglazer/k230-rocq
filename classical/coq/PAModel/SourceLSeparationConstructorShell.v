(** Literal outer forall/guard shell of the L-Separation constructor. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded
  SourceRelativizationBounds SourceRelativeSchemaConstructors SourceSchemaRelativization QuotationSchemaSkeleton
  SourceLSeparationWitnessShift SourceLDefinableProfile SourceFunctionalityShells SourceWFSeparationConstructor
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_relative_separation_witness_shell M domain body target :
  sf_relative_separation_constructor M domain body target ->exists witness outer,
    code_relation M(L_definable_profile_environment body domain)(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness /\
    sf_relation M SFImpl domain witness outer /\sf_relation M SFAll outer(zeroM M)target.
Proof.
  intro HTarget.
  destruct(code_relation_total M(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))
    (L_definable_profile_environment body domain)) as(witness&HWitness).
  destruct(source_lsep_indexed_split M domain body 2 witness HWitness)
    as(zx&za&rhs&lr&rl&point&guarded&all&inner&HZX&HZA&HRhs&HLR&HRL&HPoint&HGuard&HAll&HInner&HEx).
  destruct(sf_relation_total M SFImpl domain witness) as(outer&HOuter).
  destruct(sf_relation_total M SFAll outer(zeroM M)) as(other&HOther).
  assert(HOtherGraph:sf_relative_separation_constructor M domain body other).
  { unfold sf_relative_separation_constructor. rewrite relative_separation_skeleton_exact.
    unfold E_sf_relative_separation,E_sf_relative_all,E_sf_relative_ex,E_sf_all,E_sf_ex,E_sf_iff,E_sf_mem,skeleton_relative_environment.
    functionality_graph. }
  pose proof(code_relation_functional M _ _ target other HTarget HOtherGraph) as E. subst other.
  exists witness,outer. repeat first[assumption|split].
Qed.

Theorem source_full_relative_separation_outer M b c n u v sb sc sn domain body witness target count :
  source_bounded M domain(code_numeral M 1) ->source_bounded M body(succM M(succM M(succM M count))) ->
  context_bounded M b c n count ->sf_relative_separation_constructor M domain body target ->
  code_relation M(L_definable_profile_environment body domain)(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness ->
  context_shift M b c n u v ->environment_cons M u v n domain sb sc sn ->
  source_full_prv M sb sc sn witness ->source_full_prv M b c n target.
Proof.
  intros HD HB HC HTarget HWitness HShift HCons PWitness.
  destruct(source_relative_separation_witness_shell M domain body target HTarget) as(witness'&outer&HWitness'&HOuter&HAll).
  pose proof(code_relation_functional M _ _ witness witness' HWitness HWitness') as E. subst witness'.
  pose proof(source_relative_separation_bound M domain body target count HD HB HTarget) as BTarget.
  pose proof(proj1(source_bounded_accept_unary M SFAll outer target count(or_introl eq_refl)HAll)BTarget) as BOuter.
  pose proof(context_shift_preserves_bound M b c n u v count HShift HC) as HUC.
  pose proof(full_source_II M u v n domain witness outer sb sc sn(ex_intro _(succM M count)(conj BOuter HUC))PWitness HCons HOuter) as POuter.
  exact(full_source_AllI M b c n outer target u v(ex_intro _ count(conj BTarget HC))POuter HShift HAll).
Qed.
Print Assumptions source_relative_separation_witness_shell.
Print Assumptions source_full_relative_separation_outer.

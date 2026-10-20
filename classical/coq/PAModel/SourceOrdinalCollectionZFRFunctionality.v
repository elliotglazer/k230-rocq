(** Actual uniform functionality of the literal least-ordinal relation.
    The mathematical uniqueness deduction is closed with two ordinary II
    rules and three AllI rules over an actual closed ZFR axiom context. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
  SchemaConstructorBounds SourceBounded NumericalContexts NumericalEnvironments NumericalSourceFull SourceInstantiationConstructors
  SchemaRenamingDescriptors SchemaRenamingBounds SourceFunctionalityShells SourceProofWeakening
  SourceTraceBounds SourceOrdinalPredicate SourceOrdinalCollectionRecipe SourceOrdinalCollectionUnique
  SourceOrdinalTrichotomy SourceSetTheoryDescriptors SourceDescriptorProvability SourceDescriptorClosure
  SourceZFRProvability SourceLeastOrdinalWitness.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_oc_functionality M phi oc a b functionality count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  schema_renaming M RepA oc a ->schema_renaming M RepB oc b ->
  source_functionality_graph M a b functionality ->source_zfr_provable M functionality.
Proof.
  intros HB HOC HA HBB HF.
  pose proof (source_oc_form_bounded M _ phi oc count (source_ordinal_predicate_bounded M) HB HOC) as HOCBound.
  pose proof (schema_replacement_a_bound M oc a count HOCBound HA) as HABound.
  pose proof (schema_replacement_b_bound M oc b count HOCBound HBB) as HBBound.
  destruct (sf_relation_total M SFEqual (code_numeral M 1) (zeroM M)) as (equal&HEqual).
  destruct (source_functionality_shell M a b equal functionality HEqual HF)
    as (rhs&point&p1&p2&HRight&HPoint&HAll1&HAll2&HAll3).
  destruct (code_relation_total M ordinal_trichotomy_expression
    (schema_env3 (code_numeral M 1) (zeroM M) (zeroM M))) as (law&HLaw).
  destruct (source_zfr_ordinal_trichotomy M _ law HLaw) as (cb&cc&cn&HC&PLaw).
  pose proof (source_zfr_context_closed M cb cc cn HC) as HClosed.
  set (bound:=succM M (succM M (succM M count))).
  assert (HContext:context_bounded M cb cc cn bound).
  { exact (context_bounded_monotone M cb cc cn (zeroM M) bound HClosed (coding_zero_lt_succ M bound)). }
  assert (HEBound:source_bounded M equal bound).
  { apply (proj2 (source_bounded_accept_atom M SFEqual _ _ equal bound (or_intror eq_refl) HEqual)).
    split;unfold bound;schema_small_index. }
  assert (HRightBound:source_bounded M rhs bound).
  { exact (proj2 (source_bounded_accept_binary M SFImpl b equal rhs bound
      (or_intror (or_intror eq_refl)) HRight) (conj HBBound HEBound)). }
  assert (HPointBound:source_bounded M point bound).
  { exact (proj2 (source_bounded_accept_binary M SFImpl a rhs point bound
      (or_intror (or_intror eq_refl)) HPoint) (conj HABound HRightBound)). }
  destruct (environment_cons_total M cb cc cn a) as (u&v&l&HConsA).
  destruct (environment_cons_total M u v l b) as (x&y&m&HConsB).
  assert (HAC:context_bounded M u v l bound).
  { exact (proj2 (context_bounded_cons M cb cc cn a u v l bound HConsA) (conj HABound HContext)). }
  assert (HABC:context_bounded M x y m bound).
  { exact (proj2 (context_bounded_cons M u v l b x y m bound HConsB) (conj HBBound HAC)). }
  assert (IA:context_included M cb cc cn u v l) by exact (source_cons_tail_inclusion M _ _ _ _ _ _ _ HConsA).
  assert (IAB:context_included M cb cc cn x y m).
  { intros f HF'. apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HConsB f). exact (IA f HF'). }
  assert (PA:source_full_prv M x y m a).
  { apply full_source_Ctx;[exists bound;auto|].
    apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HConsB).
    apply (proj2 (context_member_cons M cb cc cn a u v l a HConsA)). now left. }
  assert (PB:source_full_prv M x y m b).
  { apply full_source_Ctx;[exists bound;auto|].
    apply (proj2 (context_member_cons M u v l b x y m b HConsB)). now left. }
  assert (PE:source_full_prv M x y m equal).
  { apply (source_full_oc_unique M x y m (succM M (succM M count)) bound phi oc a b law equal);
      try assumption;[unfold bound;schema_small_index|].
    exact (source_full_prv_weaken_bounded M cb cc cn x y m law bound PLaw IAB HABC). }
  assert (PRight:source_full_prv M u v l rhs).
  { exact (full_source_II M u v l b equal rhs x y m
      (ex_intro _ bound (conj HRightBound HAC)) PE HConsB HRight). }
  assert (PPoint:source_full_prv M cb cc cn point).
  { exact (full_source_II M cb cc cn a rhs point u v l
      (ex_intro _ bound (conj HPointBound HContext)) PRight HConsA HPoint). }
  apply (proj1 (source_zfr_descriptor_provable M functionality)).
  apply (source_descriptor_provable_all M ZFRSourceDescriptor p2 functionality);[|exact HAll3].
  apply (source_descriptor_provable_all M ZFRSourceDescriptor p1 p2);[|exact HAll2].
  apply (source_descriptor_provable_all M ZFRSourceDescriptor point p1);[|exact HAll1].
  exists cb,cc,cn. split;[exact (proj2 (source_zfr_descriptor_context M cb cc cn) HC)|exact PPoint].
Qed.

Print Assumptions source_zfr_oc_functionality.

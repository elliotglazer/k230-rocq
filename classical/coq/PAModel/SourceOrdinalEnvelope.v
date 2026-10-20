(** Retain the actual least-ordinal Replacement range and construct an
    ordinal containing every one of its members as a subset. The range
    proof is ordinary source provability; the upper bound is supplied by
    the fixed, proved ordinal-union theorem. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded NumericalContexts NumericalEnvironments
  NumericalRenaming NumericalSourceFull SourceProofWeakening SourceQuantifierRules SourceExistentialMap
  SourceClosedContextShift SourceRelativizationBounds SourceTraceBounds SourcePropositionalRebase
  SchemaRenamingDescriptors SourceOrdinalPredicate SourceOrdinalCollectionRecipe
  SourceReplacementCollector SourceOrdinalRangeMembers SourceOrdinalUnion
  SourceSetTheoryDescriptors SourceDescriptorProvability SourceZFRProvability SourceFiniteProofContexts.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_ordinal_upper_bound M upper k :
  source_ordinal_upper_graph M upper ->source_bounded M upper (succM M k).
Proof.
  intro HG.
  assert (HB:schema_expression_bound M (fun _=>source_ordinal_predicate_code M)
    E_ordinal_range_upper (succM M k)).
  { unfold E_ordinal_range_upper,E_sf_ex,E_sf_all,E_sf_mem.
    repeat schema_constructor_bound;try schema_small_index.
    exact (sr_domain_bound_succ M _ (succM M k) (source_ordinal_predicate_bounded M)). }
  exact (HB upper HG).
Qed.

Theorem source_ordinal_upper_law_split M law :source_ordinal_upper_law_graph M law ->
  exists members upper,source_ordinal_members_graph M members /\source_ordinal_upper_graph M upper /\
    sf_relation M SFImpl members upper law.
Proof.
  intro H. unfold source_ordinal_upper_law_graph,E_ordinal_range_upper_law in H.
  exact (schema_expression_split M _ SFImpl _ _ law H).
Qed.

Theorem source_zfr_oc_ordinal_envelope M phi oc matrix profile collector :
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->schema_renaming M RepC oc matrix ->
  source_replacement_profile_graph M matrix profile ->sf_relation M SFEx profile (zeroM M) collector ->
  source_zfr_provable M collector ->
  exists upper decorated envelope,source_ordinal_upper_graph M upper /\
    sf_relation M SFAnd profile upper decorated /\sf_relation M SFEx decorated (zeroM M) envelope /\
    source_zfr_provable M envelope.
Proof.
  intros HOC HMatrix HProfile HCollector PCollector.
  destruct (code_relation_total M E_ordinal_range_upper_law (fun _=>source_ordinal_predicate_code M))
    as (law&HLaw).
  pose proof (source_zfr_ordinal_upper_law M law HLaw) as PLaw.
  destruct (source_ordinal_upper_law_split M law HLaw) as (members&upper&HMembers&HUpper&HImp).
  assert (Premises:forall f,In f [collector;law] ->source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f [<-|[<-|[]]];apply (proj2 (source_zfr_descriptor_provable M _));assumption. }
  destruct (source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises) as (b&c&n&HC&P).
  pose proof (P collector (or_introl eq_refl)) as PC.
  pose proof (P law (or_intror (or_introl eq_refl))) as PL.
  destruct (source_full_prv_wellformed M b c n collector PC) as (k&HCollectorBound&HCk).
  pose proof (proj1 (source_bounded_accept_unary M SFEx profile collector k
    (or_intror eq_refl) HCollector) HCollectorBound) as HProfileBound.
  pose proof (source_ordinal_upper_bound M upper k HUpper) as HUpperBound.
  destruct (sf_relation_total M SFAnd profile upper) as (decorated&HDecorated).
  destruct (sf_relation_total M SFEx decorated (zeroM M)) as (envelope&HEnvelope).
  assert (HDecoratedBound:source_bounded M decorated (succM M k)).
  { exact (proj2 (source_bounded_accept_binary M SFAnd profile upper decorated _
      (or_introl eq_refl) HDecorated) (conj HProfileBound HUpperBound)). }
  assert (HEnvelopeBound:source_bounded M envelope k).
  { exact (proj2 (source_bounded_accept_unary M SFEx decorated envelope k
      (or_intror eq_refl) HEnvelope) HDecoratedBound). }
  pose proof (source_closed_context_shift_self M b c n (proj1 HC)) as HShift.
  destruct (environment_cons_total M b c n profile) as (u&v&l&HCons).
  assert (HCs:context_bounded M b c n (succM M k)).
  { exact (context_bounded_monotone M b c n (zeroM M) (succM M k) (proj1 HC)
      (coding_zero_lt_succ M (succM M k))). }
  assert (HBranch:context_bounded M u v l (succM M k)).
  { exact (proj2 (context_bounded_cons M b c n profile u v l _ HCons) (conj HProfileBound HCs)). }
  assert (PP:source_full_prv M u v l profile).
  { apply full_source_Ctx;[exists (succM M k);auto|].
    apply (proj2 (context_member_cons M b c n profile u v l profile HCons)). now left. }
  destruct (source_full_oc_range_members M u v l phi oc matrix profile HOC HMatrix HProfile PP)
    as (members'&HMembers'&PMembers).
  pose proof (code_relation_functional M _ _ members' members HMembers' HMembers) as EM.
  subst members'.
  assert (PU:source_full_prv M u v l upper).
  { exact (full_source_IE M u v l members upper law
      (ex_intro _ (succM M k) (conj HUpperBound HBranch))
      (source_full_prv_weaken_bounded M b c n u v l law _ PL
        ltac:(intros f HF;apply (proj2 (context_member_cons M b c n profile u v l f HCons));now right)
        HBranch) PMembers HImp). }
  assert (PD:source_full_prv M u v l decorated).
  { exact (full_source_CI M u v l profile upper decorated
      (ex_intro _ (succM M k) (conj HDecoratedBound HBranch)) PP PU HDecorated). }
  destruct (numerical_renaming_total M envelope (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (shifted&HEnvelopeShift).
  exists upper,decorated,envelope. split;[exact HUpper|]. split;[exact HDecorated|]. split;[exact HEnvelope|].
  exists b,c,n. split;[exact (proj1 (source_zfr_descriptor_context M b c n) HC)|].
  exact (source_full_exists_map M b c n profile decorated collector envelope b c u v l shifted
    (ex_intro _ k (conj HEnvelopeBound HCk)) HCollector HEnvelope HShift HCons HEnvelopeShift PC PD).
Qed.

Print Assumptions source_ordinal_upper_bound.
Print Assumptions source_ordinal_upper_law_split.
Print Assumptions source_zfr_oc_ordinal_envelope.

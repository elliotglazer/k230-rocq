(** Actual Pc carrier-equality transport at arbitrary internally coded
    names, obtained by three genuine AllE steps and simultaneous reopening. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitution NumericalInstantiation SourceD0Recipe SourceDn SourceDnBounds SourceQfFunctionality
  SourcePieceClosure SourcePieceCarrierMaps SourceFiniteCutoffShift SourceHierarchySyntax SourceDnCarrierEquality
  SourceFunctionalityShells SourcePropositionalTemplates SourcePropositionalSubstitution SourceTripleSpecialization
  SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.

Definition source_pc_carrier_template:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition source_pc_carrier_environment {A:Type}(eq before after:A)(i:nat):=match i with 0=>eq|1=>before|_=>after end.

Theorem source_zfr_pc_carrier_equality M domain level count phi d X Y eq before after map law:
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M count) ->
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->sf_relation M SFEqual X Y eq ->
  source_pc_instance M domain level count phi d X before ->source_pc_instance M domain level count phi d Y after ->
  sf_relation M SFImpl before after map ->sf_relation M SFImpl eq map law ->source_zfr_provable M law.
Proof.
  intros HD HB HLevel HE(d0&dn&rb&rc&H0&HN&HR&HBefore)(d0'&dn'&sb&sc&H0'&HN'&HS&HAfter)HMap HLaw.
  pose proof(source_d0_recipe_functional M domain level phi d0' d0 H0' H0) as E. subst d0'.
  pose proof(source_dn_functional M count d0 dn' dn HN' HN) as E. subst dn'.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  pose proof(source_pc_dn_bounded M domain level count phi d0 dn HD HL HB H0 HN) as BDN.
  destruct(source_cutoff_shift_total M 2 dn) as(a&HA).
  destruct(source_cutoff_shift_total M 1 dn) as(b&HB').
  destruct(sf_relation_total M SFEqual(code_numeral M 1)(code_numeral M 2)) as(condition&HCondition).
  destruct(sf_relation_total M SFImpl a b) as(rawMap&HRawMap).
  destruct(sf_relation_total M SFImpl condition rawMap) as(point&HPoint).
  pose proof(source_zfr_dn_carrier_equality M domain level phi count d0 dn a b condition rawMap point
    HD HL HB HLevel H0 HN HA HB' HCondition HRawMap HPoint) as PPoint.
  destruct(sf_relation_total M SFAll point(zeroM M)) as(inner&HInner).
  destruct(sf_relation_total M SFAll inner(zeroM M)) as(middle&HMiddle).
  destruct(sf_relation_total M SFAll middle(zeroM M)) as(outer&HOuter).
  pose proof(source_descriptor_provable_all M ZFRSourceDescriptor point inner(proj2(source_zfr_descriptor_provable M point)PPoint)HInner) as PInner.
  pose proof(source_descriptor_provable_all M ZFRSourceDescriptor inner middle PInner HMiddle) as PMiddle.
  destruct(source_descriptor_provable_all M ZFRSourceDescriptor middle outer PMiddle HOuter) as(ub&uc&un&HContext&POuter).
  destruct(source_triple_prefix_total M d X Y) as(tb&tc&HTriple).
  pose proof(source_pc_carrier_cutoff_specialization M false dn a d X Y tb tc rb rc before BDN HA HTriple HR HBefore) as HSubBefore.
  pose proof(source_pc_carrier_cutoff_specialization M true dn b d X Y tb tc sb sc after BDN HB' HTriple HS HAfter) as HSubAfter.
  assert(HSubEq:numerical_substitution M condition tb tc(code_numeral M 3)(zeroM M)eq).
  { apply(proj2(numerical_substitution_equal M(code_numeral M 1)(code_numeral M 2)condition tb tc(code_numeral M 3)(zeroM M)eq HCondition)).
    exists X,Y. exact(conj(proj1(proj2 HTriple))(conj(proj2(proj2 HTriple))HE)). }
  assert(HPointGraph:code_relation M(source_pc_carrier_environment condition a b)(source_prop_expression source_pc_carrier_template)point).
  { unfold source_pc_carrier_template,source_prop_expression. functionality_graph. }
  assert(HNamedGraph:code_relation M(source_pc_carrier_environment eq before after)(source_prop_expression source_pc_carrier_template)law).
  { unfold source_pc_carrier_template,source_prop_expression. functionality_graph. }
  assert(HSub:numerical_substitution M point tb tc(code_numeral M 3)(zeroM M)law).
  { apply(source_prop_expression_substitution M(source_pc_carrier_environment condition a b)(source_pc_carrier_environment eq before after)
      tb tc(code_numeral M 3)(zeroM M)source_pc_carrier_template).
    - intros[|[|i]];cbn[source_pc_carrier_environment];assumption.
    - exact HPointGraph.
    - exact HNamedGraph. }
  pose proof(source_cutoff_shift_bounded M 2 dn a(zeroM M)BDN HA) as BA.
  pose proof(source_cutoff_shift_bounded M 1 dn b(code_numeral M 1)BDN HB') as BB.
  pose proof(proj2(source_bounded_accept_atom M SFEqual(code_numeral M 1)(code_numeral M 2)condition(code_numeral M 3)
    (or_intror eq_refl)HCondition)(conj (proj2(coding_lt_succ_cancel M(zeroM M)(code_numeral M 2))(coding_zero_lt_succ M(code_numeral M 1)))(coding_lt_succ M(code_numeral M 2)))) as BC.
  pose proof(source_prop_template_bound M(source_pc_carrier_environment condition a b)source_pc_carrier_template(code_numeral M 3)
    ltac:(intros[|[|i]];cbn[source_pc_carrier_environment];assumption)point HPointGraph) as BPoint.
  exists ub,uc,un. split;[exact(proj1(source_zfr_descriptor_context M ub uc un)HContext)|].
  exact(source_full_triple_specialize M ub uc un point inner middle outer Y X d tb tc law(code_numeral M 3)
    BPoint HInner HMiddle HOuter HTriple HSub POuter).
Qed.

Print Assumptions source_zfr_pc_carrier_equality.

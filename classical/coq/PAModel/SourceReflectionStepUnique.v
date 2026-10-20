(** Two least-Cond ordinal-step witnesses are equal, by actual ordinal
    trichotomy and the two literal universal minimality exclusions. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SubstitutionSource NumericalContexts NumericalEnvironments NumericalSourceFull NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceDomainInstances SourceOrdinalPredicate SourceReflectionCondition SourceReflectionConditionTransport SourceReflectionConditionBounds SourceReflectionStep
  SourcePieceConjunctionBounds SourceOrdinalTrichotomy SourceOrdinalCollectionUnique SourceMinimalUniqueness SourceOrdinalUniquenessProgram
  SourcePieceBoundMaxJoint SourceDerivedRules SourcePropositionalTemplates SourceFunctionalityShells SourceProofWeakening SourceTraceBounds
  SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_reflection_candidate_instantiation M domain level sb sc n x candidate t value:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)candidate ->
  source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n x t value ->
  numerical_instantiation M candidate t value.
Proof.
  intros HD HL HV HC HVa. destruct(substitution_singleton_total M t) as(rb&rc&HHead&_).
  destruct(numerical_substitution_total M candidate rb rc(code_numeral M 1)(zeroM M)) as(out&HOut).
  pose proof(source_reflection_condition_substitution M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)candidate
    rb rc(code_numeral M 1)(zeroM M)x t out HD HL(source_ordinal_predicate_bounded M)HV HC HOut
    (substitution_singleton_tail M rb rc x)HHead) as HO.
  pose proof(source_reflection_condition_functional M domain level(source_ordinal_predicate_code M)sb sc n x t out value HO HVa) as E.
  subst out. exists rb,rc. auto.
Qed.

Theorem source_full_reflection_step_unique M b c l domain level sb sc n x d e a bstep triLaw equal k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  coding_lt M x k ->coding_lt M d k ->coding_lt M e k ->context_bounded M b c l k ->
  source_reflection_step M domain level sb sc n x d a ->source_reflection_step M domain level sb sc n x e bstep ->
  code_relation M(fun i=>match i with 0=>d|1=>e|_=>zeroM M end)ordinal_trichotomy_expression triLaw ->
  sf_relation M SFEqual d e equal ->source_full_prv M b c l triLaw ->
  source_full_prv M b c l a ->source_full_prv M b c l bstep ->source_full_prv M b c l equal.
Proof.
  intros HD HL HV HX HDk HEk HC
    (od&predD&candD&memD&negD&pointD&allD&bothD&HOD&HPredD&HCandD&HMemD&HNegD&HPointD&HAllD&HBothD&HOutD)
    (oe&predE&candE&memE&negE&pointE&allE&bothE&HOE&HPredE&HCandE&HMemE&HNegE&HPointE&HAllE&HBothE&HOutE)
    HTriLaw HEqual PTriLaw PD PE.
  pose proof(source_reflection_candidate_instantiation M domain level sb sc n x candD e predE HD HL HV HCandD HPredE) as HID.
  pose proof(source_reflection_candidate_instantiation M domain level sb sc n x candE d predD HD HL HV HCandE HPredD) as HIE.
  destruct(source_exclusion_instantiation M candD pointD memD negD d e predE HMemD HNegD HPointD HID)
    as(right&notE&rex&HRight&HNotE&HRex&HIRex).
  destruct(source_exclusion_instantiation M candE pointE memE negE e d predD HMemE HNegE HPointE HIE)
    as(left&notD&lex&HLeft&HNotD&HLex&HILex).
  destruct(source_ordinal_trichotomy_shell M _ triLaw HTriLaw) as(od'&oe'&tail&tri&first&left'&equal'&right'
    &HOD'&HOE'&HTail&HTri&HFirst&HOr&HLeft'&HEqual'&HRight').
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)d od' od HOD' HOD) as E. subst od'.
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)e oe' oe HOE' HOE) as E. subst oe'.
  pose proof(sf_relation_functional M SFMember d e left' left HLeft' HLeft) as E. subst left'.
  pose proof(sf_relation_functional M SFMember e d right' right HRight' HRight) as E. subst right'.
  pose proof(sf_relation_functional M SFEqual d e equal' equal HEqual' HEqual) as E. subst equal'.
  destruct(source_full_piece_conjunction_components M b c l bothD allD a HOutD PD) as[PBothD PAllD].
  destruct(source_full_piece_conjunction_components M b c l od predD bothD HBothD PBothD) as[POD PPredD].
  destruct(source_full_piece_conjunction_components M b c l bothE allE bstep HOutE PE) as[PBothE PAllE].
  destruct(source_full_piece_conjunction_components M b c l oe predE bothE HBothE PBothE) as[POE PPredE].
  pose proof(source_full_modus_ponens M b c l od tail triLaw HTail PTriLaw POD) as PTail.
  pose proof(source_full_modus_ponens M b c l oe tri tail HTri PTail POE) as PTri.
  set(rho:=oc_unique_environment left equal right predD predE).
  assert(HRho:forall i,source_bounded M(rho i)k).
  { intros[|[|[|[|i]]]];cbn[rho oc_unique_environment].
    - exact(proj2(source_bounded_accept_atom M SFMember d e left k(or_introl eq_refl)HLeft)(conj HDk HEk)).
    - exact(proj2(source_bounded_accept_atom M SFEqual d e equal k(or_intror eq_refl)HEqual)(conj HDk HEk)).
    - exact(proj2(source_bounded_accept_atom M SFMember e d right k(or_introl eq_refl)HRight)(conj HEk HDk)).
    - exact(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n x d predD k HD HL(source_ordinal_predicate_bounded M)HV HX HDk HPredD).
    - exact(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n x e predE k HD HL(source_ordinal_predicate_bounded M)HV HX HEk HPredE). }
  apply(source_full_minimal_uniqueness M rho k b c l tri lex rex pointE allE pointD allD d e HRho HC).
  - unfold ordinal_unique_tri,source_prop_expression. functionality_graph.
  - unfold ordinal_unique_left_exclusion,source_prop_expression. functionality_graph.
  - unfold ordinal_unique_right_exclusion,source_prop_expression. functionality_graph.
  - exact HAllE.
  - exact HAllD.
  - exact HILex.
  - exact HIRex.
  - exact PTri.
  - exact PPredD.
  - exact PPredE.
  - exact PAllE.
  - exact PAllD.
Qed.

Theorem source_zfr_reflection_step_unique M domain level sb sc n x d e a bstep equal tail law k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  coding_lt M x k ->coding_lt M d k ->coding_lt M e k ->
  source_reflection_step M domain level sb sc n x d a ->source_reflection_step M domain level sb sc n x e bstep ->
  sf_relation M SFEqual d e equal ->sf_relation M SFImpl bstep equal tail ->sf_relation M SFImpl a tail law ->source_zfr_provable M law.
Proof.
  intros HD HL HV HX HDk HEk HA HB HEqual HTail HLaw.
  destruct(code_relation_total M ordinal_trichotomy_expression(fun i=>match i with 0=>d|1=>e|_=>zeroM M end)) as(triLaw&HTriLaw).
  destruct(source_zfr_ordinal_trichotomy M _ triLaw HTriLaw) as(b&c&l&HCtx&PTriLaw).
  pose proof(source_zfr_context_closed M b c l HCtx) as BCtx0.
  pose proof(context_bounded_monotone M b c l(zeroM M)k BCtx0(coding_zero_lt_succ M k)) as BCtx.
  pose proof(source_reflection_step_bounded M domain level sb sc n x d a k HD HL HV HX HDk HA) as BA.
  pose proof(source_reflection_step_bounded M domain level sb sc n x e bstep k HD HL HV HX HEk HB) as BB.
  pose proof(proj2(source_bounded_accept_atom M SFEqual d e equal k(or_intror eq_refl)HEqual)(conj HDk HEk)) as BEq.
  pose proof(proj2(source_bounded_accept_binary M SFImpl bstep equal tail k(or_intror(or_intror eq_refl))HTail)(conj BB BEq)) as BTail.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a tail law k(or_intror(or_intror eq_refl))HLaw)(conj BA BTail)) as BLaw.
  destruct(environment_cons_total M b c l a) as(ab&ac&an&HConsA).
  pose proof(proj2(context_bounded_cons M b c l a ab ac an k HConsA)(conj BA BCtx)) as BCA.
  destruct(environment_cons_total M ab ac an bstep) as(bb&bc&bn&HConsB).
  pose proof(proj2(context_bounded_cons M ab ac an bstep bb bc bn k HConsB)(conj BB BCA)) as BCB.
  assert(PA:source_full_prv M bb bc bn a).
  { apply full_source_Ctx;[exists k;auto|]. apply(proj2(context_member_cons M ab ac an bstep bb bc bn a HConsB)). right.
    apply(proj2(context_member_cons M b c l a ab ac an a HConsA)). now left. }
  assert(PB:source_full_prv M bb bc bn bstep).
  { apply full_source_Ctx;[exists k;auto|]. apply(proj2(context_member_cons M ab ac an bstep bb bc bn bstep HConsB)). now left. }
  assert(PTri:source_full_prv M bb bc bn triLaw).
  { apply(source_full_prv_weaken_bounded M b c l bb bc bn triLaw k PTriLaw);[|exact BCB].
    intros f HF. apply(proj2(context_member_cons M ab ac an bstep bb bc bn f HConsB)). right.
    apply(proj2(context_member_cons M b c l a ab ac an f HConsA)). now right. }
  pose proof(source_full_reflection_step_unique M bb bc bn domain level sb sc n x d e a bstep triLaw equal k
    HD HL HV HX HDk HEk BCB HA HB HTriLaw HEqual PTri PA PB) as PEq.
  pose proof(full_source_II M ab ac an bstep equal tail bb bc bn(ex_intro _ k(conj BTail BCA))PEq HConsB HTail) as PNext.
  exists b,c,l. split;[exact HCtx|]. exact(full_source_II M b c l a tail law ab ac an(ex_intro _ k(conj BLaw BCtx))PNext HConsA HLaw).
Qed.

Print Assumptions source_reflection_candidate_instantiation.
Print Assumptions source_full_reflection_step_unique.
Print Assumptions source_zfr_reflection_step_unique.

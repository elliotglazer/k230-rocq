(** Initial-parameter PH consumer. Numerical name/formula bounds and the
    identity parameter map are constructed, rather than assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions Pairing SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalRenamingMaps NumericalRenaming NumericalInstantiation SourceRenamingIdentity SourceShiftSpecialization SourceFiniteFamilyBounds
 SourceOrdinalPredicate SourceCofinalGeometry SourceHierarchySyntax SourceMembershipBlocks SourcePieceConjunctionBounds
 SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations SourceReflectionKF SourceEwMonotone SourceFiniteTelescope SourceZFRProvability SourcePHFrom.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_zfr_PH_initial M domain level sb sc count K beta Lb seed
 entry params phi member ordinals cover ob subsets lb whole block goal law:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 sf_relation M SFMember seed K member ->source_cofinal_ordinals M K ordinals ->source_cofinal_cover M K Lb cover ->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ob ->
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets ->source_LL_instance M beta Lb lb ->
 source_reflection_KF M domain level sb sc count K whole ->source_membership_block M(zeroM M)Lb params block ->
 source_ew_at M domain phi Lb goal ->
 source_finite_telescope M[member;ordinals;cover;ob;subsets;lb;whole;block]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HM HO HC HOB HSub HLb HW HB HG HLaw.
 destruct(source_finite_names_bound M[K;beta;Lb;seed;params])as(bound&BN).
 assert(BK:coding_lt M K bound)by(apply BN;cbn;tauto).
 assert(Bbeta:coding_lt M beta bound)by(apply BN;cbn;tauto).
 assert(BLb:coding_lt M Lb bound)by(apply BN;cbn;tauto).
 assert(BSeed:coding_lt M seed bound)by(apply BN;cbn;tauto).
 assert(BParams:coding_lt M params bound)by(apply BN;cbn;tauto).
 pose proof(HV entry params phi HE HP)as BOriginal.
 assert(BPhi:source_bounded M phi(succM M bound)).
 { apply(SourceBoundMonotone.source_bounded_monotone M phi(succM M params)(succM M bound)BOriginal).
   apply(proj2(coding_lt_succ_cancel M params(succM M bound))).
   exact(proj2(coding_lt_succ_cases M params bound)(or_introl BParams)). }
 destruct(renaming_lift_total M(zeroM M)(zeroM M)(zeroM M)(zeroM M))as(rb&rc&rn&HRL).
 assert(HFix:renaming_fixes_bound M rb rc rn(zeroM M)(succM M params)).
 { apply(renaming_lift_fixes_bound M(zeroM M)(zeroM M)(zeroM M)(zeroM M)rb rc rn params HRL).
   intros i _. apply source_empty_renaming_lookup. }
 pose proof(numerical_renaming_identity_on_bound M phi rb rc rn(zeroM M)(succM M params)BOriginal HFix)as HR.
 apply(source_zfr_PH_from M domain level sb sc count K beta Lb seed(zeroM M)
  entry params phi rb rc rn phi member ordinals cover ob subsets lb whole block goal law bound
  HD HL HLg HV HE HP HM HO HC HOB HSub HLb HW HB HRL HR HG BPhi BK Bbeta BLb BSeed).
 - intros i HI. rewrite(coding_add_zero_r M i). exact(coding_lt_trans M i params bound HI BParams).
 - exact HLaw.
Qed.
Print Assumptions source_zfr_PH_initial.

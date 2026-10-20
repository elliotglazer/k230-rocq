(** Actual conjunction witness construction in the explicit named frame.
    The final coordinate normalization to the canonical closure recipe is
    a separate syntax step; it is not asserted by this module. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceNumeralLift FixedSourceBounds SourcePropositionalTemplates SourceDescriptorProvability
 SourceDescriptorNamedPrograms SourceRepresentationConjunctionShell SourceNamedQuantifierRules
 SourceNamedVacuity SourceNamedElimination SourceNamedVacuityImages SourceNamedDifferenceCertificates SourceNamedFiniteCalibration
 SourceNamedDifferenceFacts SourceDifferenceNumeralParameters SourceDifferenceProfile SourceRepresentationNamedWitness
 SourceRepresentativeRenaming SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
 SourceZFRProvability SourceSetTheoryDescriptors SourceRepresentationRecipe SourceRepresentationConjunctionLaw
 SourceRepresentationConjunctionFrame SourceRepresentationDifferencePoints SourceFiniteParameterProofs.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Open Scope minZFsyn.
Unset Implicit Arguments.

Definition RNC_member M i:=code_numeral M(sf_make SFMember i 2).
Definition RNC_operation1 M:=code_numeral M(sf_encode(source_difference_operation $3 $4 $5)).
Definition RNC_operation2 M:=code_numeral M(sf_encode(source_difference_operation $3 $5 $0)).
Definition RNC_middle_exists M:=code_numeral M(sf_encode(named_difference_exists 3 4 5)).
Definition RNC_final_exists M:=code_numeral M(sf_encode(named_difference_exists 3 5 0)).
Definition RNC_environment M namedL namedR result exTarget exL exR i:=match i with
 |0=>code_numeral M(sf_encode named_difference_successor)
 |1=>code_numeral M(sf_encode named_difference_closure)
 |2=>RNC_member M 3|3=>RNC_member M 4|4=>RNC_member M 5|5=>RNC_member M 0
 |6=>namedL|7=>namedR|8=>result|9=>RNC_operation1 M|10=>RNC_operation2 M
 |11=>RNC_middle_exists M|12=>RNC_final_exists M|13=>exTarget|14=>exL|15=>exR|_=>zeroM M end.

Lemma RNC_fixed_imp_graph M rho (a b:sf_form) A B :
 code_relation M rho(source_prop_expression A)(code_numeral M(sf_encode a)) ->
 code_relation M rho(source_prop_expression B)(code_numeral M(sf_encode b)) ->
 code_relation M rho(source_prop_expression(SPTImpl A B))(code_numeral M(sf_encode(a →b))).
Proof.
 intros HA HB. exact(source_prop_template_join M rho SFImpl A B
  (code_numeral M(sf_encode a))(code_numeral M(sf_encode b))(code_numeral M(sf_encode(a →b)))
  HA HB(sf_make_numeral M SFImpl(sf_encode a)(sf_encode b))).
Qed.

Lemma RNC_first_graph M l r q e a b :code_relation M(RNC_environment M l r q e a b)
 (source_prop_expression RCS_first_law)(code_numeral M(sf_encode
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→named_difference_exists 3 4 5))).
Proof.
 unfold RCS_first_law.
 refine(RNC_fixed_imp_graph M (RNC_environment M l r q e a b) named_difference_successor
  (named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→named_difference_exists 3 4 5)
  (SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 11)))) eq_refl _).
 refine(RNC_fixed_imp_graph M (RNC_environment M l r q e a b) named_difference_closure
  (($3 ∈' $2)→($4 ∈' $2)→named_difference_exists 3 4 5)
  (SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 11))) eq_refl _).
 refine(RNC_fixed_imp_graph M (RNC_environment M l r q e a b)($3 ∈' $2)
  (($4 ∈' $2)→named_difference_exists 3 4 5)
  (SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 11)) eq_refl _).
 exact(RNC_fixed_imp_graph M (RNC_environment M l r q e a b)($4 ∈' $2)(named_difference_exists 3 4 5)
  (SPTSlot 3)(SPTSlot 11)eq_refl eq_refl).
Qed.
Lemma RNC_second_graph M l r q e a b :code_relation M(RNC_environment M l r q e a b)
 (source_prop_expression RCS_second_law)(code_numeral M(sf_encode
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($5 ∈' $2)→named_difference_exists 3 5 0))).
Proof.
 unfold RCS_second_law.
 refine(RNC_fixed_imp_graph M (RNC_environment M l r q e a b) named_difference_successor
  (named_difference_closure →($3 ∈' $2)→($5 ∈' $2)→named_difference_exists 3 5 0)
  (SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 12)))) eq_refl _).
 refine(RNC_fixed_imp_graph M (RNC_environment M l r q e a b) named_difference_closure
  (($3 ∈' $2)→($5 ∈' $2)→named_difference_exists 3 5 0)
  (SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 12))) eq_refl _).
 refine(RNC_fixed_imp_graph M (RNC_environment M l r q e a b)($3 ∈' $2)
  (($5 ∈' $2)→named_difference_exists 3 5 0)
  (SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 12)) eq_refl _).
 exact(RNC_fixed_imp_graph M (RNC_environment M l r q e a b)($5 ∈' $2)(named_difference_exists 3 5 0)
  (SPTSlot 4)(SPTSlot 12)eq_refl eq_refl).
Qed.

Lemma RNC_member_bound M i :(i<8)%nat ->source_bounded M(RNC_member M i)(code_numeral M 8).
Proof.
 intro HI. apply(proj2(source_bounded_accept_atom M SFMember(code_numeral M i)(code_numeral M 2)
  (RNC_member M i)(code_numeral M 8)(or_introl eq_refl)(sf_make_numeral M SFMember i 2))).
 split;apply(proj2(fixed_source_numeral_lt_iff M _ 8));lia.
Qed.
Lemma RNC_representative_bound M rep named r :source_bounded M rep(code_numeral M 2) ->
 (r<8)%nat ->source_representative_renaming M(code_numeral M r)rep named ->
 source_bounded M named(code_numeral M 8).
Proof.
 intros HB HR HG. apply(numerical_renaming_preserves_bound M rep _ _ _ _ named(code_numeral M 2)(code_numeral M 8)HB HG).
 intros i j HI HJ. destruct(source_numeral_initial_segment M 2 i HI)as(index&HN&->).
 destruct index as[|[|index]];try lia.
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j(code_numeral M r)HJ(representative_lookup_zero M _)).
   exact(proj2(fixed_source_numeral_lt_iff M r 8)HR).
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j(code_numeral M 1)HJ
    (representative_lookup_nonzero M _ _(source_fixed_numeral_neq M 1 0 ltac:(lia)))).
   exact(proj2(fixed_source_numeral_lt_iff M 1 8)ltac:(lia)).
Qed.

Theorem source_zfr_named_conjunction_from_point M repL repR namedL namedR result condition inner body law :
 source_bounded M repL(code_numeral M 2) ->source_bounded M repR(code_numeral M 2) ->
 source_bounded M result(code_numeral M 2) ->
 source_representative_renaming M(code_numeral M 3)repL namedL ->
 source_representative_renaming M(code_numeral M 4)repR namedR ->
 sf_relation M SFAnd(RNC_operation1 M)(RNC_operation2 M)condition ->
 sf_relation M SFImpl namedR result inner ->sf_relation M SFImpl namedL inner body ->
 sf_relation M SFImpl condition body law ->source_zfr_provable M law ->
 exists matrixL matrixR matrixTarget exL exR exTarget out,
 sf_relation M SFAnd(RNC_member M 3)namedL matrixL /\
 sf_relation M SFAnd(RNC_member M 4)namedR matrixR /\
 sf_relation M SFAnd(RNC_member M 0)result matrixTarget /\
 source_named_quantifier M false(code_numeral M 3)matrixL exL /\
 source_named_quantifier M false(code_numeral M 4)matrixR exR /\
 source_named_quantifier M false(zeroM M)matrixTarget exTarget /\
 code_relation M(RNC_environment M namedL namedR result exTarget exL exR)
  (source_prop_expression RCS_result)out /\source_zfr_provable M out.
Proof.
 intros BL BR BQ HNL HNR HC HI HB HL PLaw.
 destruct(sf_relation_total M SFAnd(RNC_member M 3)namedL)as(ml&HML).
 destruct(sf_relation_total M SFAnd(RNC_member M 4)namedR)as(mr&HMR).
 destruct(sf_relation_total M SFAnd(RNC_member M 0)result)as(mt&HMT).
 destruct(source_named_quantifier_total M false(code_numeral M 3)ml)as(el&HEL).
 destruct(source_named_quantifier_total M false(code_numeral M 4)mr)as(er&HER).
 destruct(source_named_quantifier_total M false(zeroM M)mt)as(et&HET).
 set(rho:=RNC_environment M namedL namedR result et el er).
 assert(GL:code_relation M rho(source_prop_expression RCS_left)ml).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 2)(SPTSlot 6)(RNC_member M 3)namedL ml eq_refl eq_refl HML). }
 assert(GR:code_relation M rho(source_prop_expression RCS_right)mr).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 3)(SPTSlot 7)(RNC_member M 4)namedR mr eq_refl eq_refl HMR). }
 assert(GT:code_relation M rho(source_prop_expression RCS_target)mt).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 5)(SPTSlot 8)(RNC_member M 0)result mt eq_refl eq_refl HMT). }
 set(mm:=code_numeral M(sf_encode(named_difference_matrix 3 4 5))).
 set(mf:=code_numeral M(sf_encode(named_difference_matrix 3 5 0))).
 assert(GM:code_relation M rho(source_prop_expression RCS_middle)mm).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 4)(SPTSlot 9)(RNC_member M 5)(RNC_operation1 M)mm eq_refl eq_refl
    (sf_make_numeral M SFAnd(sf_make SFMember 5 2)(sf_encode(source_difference_operation $3 $4 $5)))). }
 assert(GF:code_relation M rho(source_prop_expression RCS_final)mf).
 { exact(source_prop_template_join M rho SFAnd(SPTSlot 5)(SPTSlot 10)(RNC_member M 0)(RNC_operation2 M)mf eq_refl eq_refl
    (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode(source_difference_operation $3 $5 $0)))). }
 assert(BMT:source_bounded M mt(code_numeral M 3)).
 { exact(source_representation_witness_body_bound M result mt BQ HMT). }
 pose proof(source_named_quantifier_bound M false(zeroM M)mt et(code_numeral M 3)BMT HET)as BET.
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)repL)as(ol&HOrigL).
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)repR)as(orr&HOrigR).
 pose proof(source_representation_named_witness_bound M(code_numeral M 3)repL namedL(RNC_member M 3)ol ml el BL
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia) HNL(sf_make_numeral M SFMember 3 2)HOrigL HML HEL)as BEL.
 pose proof(source_representation_named_witness_bound M(code_numeral M 4)repR namedR(RNC_member M 4)orr mr er BR
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia) HNR(sf_make_numeral M SFMember 4 2)HOrigR HMR HER)as BER.
 assert(BOp1:source_bounded M(RNC_operation1 M)(code_numeral M 8)).
 { exact(difference_operation_parameters_bound M(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(code_numeral M 8)(RNC_operation1 M)
    (proj2(fixed_source_numeral_lt_iff M 3 8)ltac:(lia))(proj2(fixed_source_numeral_lt_iff M 4 8)ltac:(lia))
    (proj2(fixed_source_numeral_lt_iff M 5 8)ltac:(lia))(source_difference_operation_numeral_graph M 3 4 5)). }
 assert(BOp2:source_bounded M(RNC_operation2 M)(code_numeral M 8)).
 { exact(difference_operation_parameters_bound M(code_numeral M 3)(code_numeral M 5)(zeroM M)(code_numeral M 8)(RNC_operation2 M)
    (proj2(fixed_source_numeral_lt_iff M 3 8)ltac:(lia))(proj2(fixed_source_numeral_lt_iff M 5 8)ltac:(lia))
    (coding_zero_lt_succ M(code_numeral M 7))(source_difference_operation_numeral_graph M 3 5 0)). }
 assert(BMM:source_bounded M mm(code_numeral M 8)).
 { apply(proj2(source_bounded_accept_binary M SFAnd(RNC_member M 5)(RNC_operation1 M)mm(code_numeral M 8)(or_introl eq_refl)
    (sf_make_numeral M SFAnd(sf_make SFMember 5 2)(sf_encode(source_difference_operation $3 $4 $5))))). split;[apply RNC_member_bound;lia|exact BOp1]. }
 assert(BMF:source_bounded M mf(code_numeral M 8)).
 { apply(proj2(source_bounded_accept_binary M SFAnd(RNC_member M 0)(RNC_operation2 M)mf(code_numeral M 8)(or_introl eq_refl)
    (sf_make_numeral M SFAnd(sf_make SFMember 0 2)(sf_encode(source_difference_operation $3 $5 $0))))). split;[apply RNC_member_bound;lia|exact BOp2]. }
 pose proof(source_named_quantifier_bound M false(code_numeral M 5)mm(RNC_middle_exists M)(code_numeral M 8)BMM(named_difference_first_quantifier M))as BEM.
 pose proof(source_named_quantifier_bound M false(zeroM M)mf(RNC_final_exists M)(code_numeral M 8)BMF(named_difference_second_quantifier M))as BEF.
 assert(BAll:forall i,source_bounded M(rho i)(code_numeral M 8)).
 { intros[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]];cbn[rho RNC_environment].
   - exact(proj1(named_difference_fixed_bounds M)).
   - exact(proj2(named_difference_fixed_bounds M)).
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - apply RNC_member_bound;lia.
   - exact(RNC_representative_bound M repL namedL 3 BL ltac:(lia) HNL).
   - exact(RNC_representative_bound M repR namedR 4 BR ltac:(lia) HNR).
   - exact(source_bounded_monotone M result(code_numeral M 2)(code_numeral M 8)BQ(proj2(fixed_source_numeral_lt_iff M 2 9)ltac:(lia))).
   - exact BOp1.
   - exact BOp2.
   - exact BEM.
   - exact BEF.
   - exact(source_bounded_monotone M et(code_numeral M 3)(code_numeral M 8)BET(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - exact(source_bounded_monotone M el(code_numeral M 3)(code_numeral M 8)BEL(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - exact(source_bounded_monotone M er(code_numeral M 3)(code_numeral M 8)BER(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - apply source_bounded_accept_falsity. }
 assert(V0:source_prop_named_vacuity M rho(zeroM M)RCS_goal0).
 { cbn[source_prop_named_vacuity RCS_goal0 RCS_middle RCS_left RCS_right rho RNC_environment]. repeat split.
   - exact(named_difference_member_vacuous M 0 5 ltac:(lia)ltac:(lia)).
   - exact(source_finite_named_vacuity M 0(source_difference_operation $3 $4 $5)eq_refl).
   - exact(named_difference_member_vacuous M 0 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repL namedL(code_numeral M 3)(zeroM M)BL HNL
      (source_fixed_numeral_neq M 3 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(named_difference_member_vacuous M 0 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repR namedR(code_numeral M 4)(zeroM M)BR HNR
      (source_fixed_numeral_neq M 4 0 ltac:(lia))(source_fixed_numeral_neq M 1 0 ltac:(lia))).
   - exact(source_named_quantifier_is_vacuous M false(zeroM M)mt et(code_numeral M 3)BMT HET). }
 assert(V5:source_prop_named_vacuity M rho(code_numeral M 5)RCS_goal5).
 { cbn[source_prop_named_vacuity RCS_goal5 RCS_left RCS_right rho RNC_environment]. repeat split.
   - exact(named_difference_member_vacuous M 5 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repL namedL(code_numeral M 3)(code_numeral M 5)BL HNL
      (source_fixed_numeral_neq M 3 5 ltac:(lia))(source_fixed_numeral_neq M 1 5 ltac:(lia))).
   - exact(named_difference_member_vacuous M 5 4 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repR namedR(code_numeral M 4)(code_numeral M 5)BR HNR
      (source_fixed_numeral_neq M 4 5 ltac:(lia))(source_fixed_numeral_neq M 1 5 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 5 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 5 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 5)(code_numeral M 3)BET
      (proj2(fixed_source_numeral_lt_iff M 3 6)ltac:(lia))). }
 assert(V4:source_prop_named_vacuity M rho(code_numeral M 4)RCS_goal4).
 { cbn[source_prop_named_vacuity RCS_goal4 RCS_left rho RNC_environment]. repeat split.
   - exact(named_difference_member_vacuous M 4 3 ltac:(lia)ltac:(lia)).
   - exact(source_named_vacuous_representative_image M repL namedL(code_numeral M 3)(code_numeral M 4)BL HNL
      (source_fixed_numeral_neq M 3 4 ltac:(lia))(source_fixed_numeral_neq M 1 4 ltac:(lia))).
   - exact(proj1(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 4 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 4)(code_numeral M 3)BET
      (proj2(fixed_source_numeral_lt_iff M 3 5)ltac:(lia))). }
 assert(V3:source_prop_named_vacuity M rho(code_numeral M 3)RCS_goal3).
 { cbn[source_prop_named_vacuity RCS_goal3 rho RNC_environment]. repeat split.
   - exact(source_named_vacuous_above_bound M er(code_numeral M 3)(code_numeral M 3)BER(coding_lt_succ M(code_numeral M 3))).
   - exact(proj1(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(proj2(named_difference_conditions_vacuous M 3 ltac:(auto))).
   - exact(source_named_vacuous_above_bound M et(code_numeral M 3)(code_numeral M 3)BET(coding_lt_succ M(code_numeral M 3))). }
 assert(PPoint:source_descriptor_template M ZFRSourceDescriptor rho RCS_point_law).
 { intros f HF.
   assert(G:code_relation M rho(source_prop_expression RCS_point_law)law).
   { apply(source_prop_template_join M rho SFImpl(SPTAnd(SPTSlot 9)(SPTSlot 10))
      (SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 7)(SPTSlot 8)))condition body law);[| |exact HL].
     - exact(source_prop_template_join M rho SFAnd(SPTSlot 9)(SPTSlot 10)(RNC_operation1 M)(RNC_operation2 M)condition eq_refl eq_refl HC).
     - apply(source_prop_template_join M rho SFImpl(SPTSlot 6)(SPTImpl(SPTSlot 7)(SPTSlot 8))namedL inner body eq_refl);[|exact HB].
       exact(source_prop_template_join M rho SFImpl(SPTSlot 7)(SPTSlot 8)namedR result inner eq_refl eq_refl HI). }
   rewrite(code_relation_functional M _ rho f law HF G).
   exact(proj2(source_zfr_descriptor_provable M law)PLaw). }
 assert(PF:source_descriptor_template M ZFRSourceDescriptor rho RCS_first_law).
 { intros f HF. rewrite(code_relation_functional M _ rho f _ HF(RNC_first_graph M namedL namedR result et el er)).
   exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_named_difference_first M)). }
 assert(PS:source_descriptor_template M ZFRSourceDescriptor rho RCS_second_law).
 { intros f HF. rewrite(code_relation_functional M _ rho f _ HF(RNC_second_graph M namedL namedR result et el er)).
   exact(proj2(source_zfr_descriptor_provable M _)(source_zfr_named_difference_second M)). }
 pose proof(source_descriptor_conjunction_witness_shell M ZFRSourceDescriptor rho(code_numeral M 8)
  (zeroM M)(code_numeral M 5)(code_numeral M 3)(code_numeral M 4)mf mm ml mr mt
  BAll GF GM GL GR GT(named_difference_second_quantifier M)(named_difference_first_quantifier M)HEL HER HET
  V0 V5 V4 V3 PPoint PF PS)as PResult.
 destruct(code_relation_total M(source_prop_expression RCS_result)rho)as(out&HOut).
 exists ml,mr,mt,el,er,et,out.
 exact(conj HML(conj HMR(conj HMT(conj HEL(conj HER(conj HET(conj HOut
  (proj1(source_zfr_descriptor_provable M out)(PResult out HOut))))))))).
Qed.

Print Assumptions source_zfr_named_conjunction_from_point.

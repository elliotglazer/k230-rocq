(** Construct a complete projection frame for arbitrary internal matrices.
    Input hypotheses are syntax, numeric bounds, and hygiene only. All fixed
    Op4/extension facts and all actual source-calculus proof steps are supplied. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent SetSchemaConstructors SourceBounded SourceBoundMonotone
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram SourceIffGraphs SourceFiniteFamilyBounds
 SourceDescriptorProvability SourceZFRProvability SourceProjectionHeadFrame SourceProjectionHeadAssembly
 SourceProjectionHeadPoint SourceProjectionGuardedTransfer SourceProjectionProfilePoint SourceProjectionFiniteBinders SourceProjectionFiniteSyntax
 SourceProjectionExtensionBinder SourceProjectionOperationFixed SourceEnvironmentExtensionScopes SourceEnvironmentCarrierClosure
 SourceRepresentationHeadCalibration SourceRepresentationSuccessorHead SourceRepresentationRecipe SourceExistentialPointCalibration
 SourceEnvironmentHeadCalibration SourceDefinabilityPrimitives SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterProofs SourceParameterGraphs
 SourceNamedQuantifierRules SourceNamedVacuity SourceNamedElimination SourceNamedHoleEvaluation SourceNamedScopes SourceNamedScopeBinding NativeKBundle.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition projection_head_values M named theta extension childmember valuemember exprevious allchild head exextension inner allpoint profile targetex inAn inResult op coverage target allguard i:=match i with
 |0=>named|1=>extension|2=>childmember|3=>theta|4=>valuemember|5=>exprevious|6=>allchild|7=>head|8=>exextension
 |9=>inner|10=>allpoint|11=>profile|12=>targetex|13=>inAn|14=>inResult|15=>op|16=>coverage|17=>target|18=>allguard|_=>zeroM M end.
Definition projection_child_names(M:Model)(a e p child:carrier M)i:=match i with 0=>a|1=>e|2=>p|_=>child end.
Definition projection_child_template:=NNTAll(CEvar 0)(NNTImpl(NNTAtom false(CEvar 0)(CEconst 1))
 (NNTAll(CEvar 1)(NNTImpl(NNTEx(CEvar 2)(NNTAnd(NNTHole 0)(NNTHole 1)))
 (NNTIff(NNTAtom false(CEvar 1)(CEvar 3))(NNTHole 2))))).
Definition projection_child_holes(M:Model)(named extension theta:carrier M)i:=match i with 0=>named|1=>extension|_=>theta end.
Definition projection_parent_holes(M:Model)(named theta:carrier M)i:=match i with 0=>named|_=>theta end.
Theorem source_zfr_projection_head_total M an child p e a named theta head coverage inAn coveragebody target extension k:
 source_bounded M named(succM M p) ->source_bounded M theta(succM M a) ->
 source_bounded M head k ->source_bounded M coverage k ->
 coding_lt M an k ->coding_lt M child k ->coding_lt M(code_numeral M 1)k ->coding_lt M(zeroM M)k ->
 ~coding_lt M p k ->~coding_lt M e k ->~coding_lt M a k ->coding_lt M p a ->coding_lt M a e ->
 sf_relation M SFMember p an inAn ->sf_relation M SFImpl named inAn coveragebody ->
 source_named_quantifier M true p coveragebody coverage ->
 code_relation M(environment_extension_names M p e a)
  (source_parameter_expression source_three_parameter_names source_def_extension021)extension ->
 source_hole_named_evaluation M(projection_child_names M a e p child)(projection_child_holes M named extension theta)projection_child_template head ->
 source_hole_named_evaluation M(existential_point_names M p a)(projection_parent_holes M named theta)existential_point_template target ->
 exists op inner body law,
 code_relation M(projection_five_values an child(code_numeral M 1)(zeroM M)p)
  (source_parameter_expression(source_finite_parameter_names 4)projection_operation4)op /\
 sf_relation M SFImpl coverage target inner /\sf_relation M SFImpl head inner body /\sf_relation M SFImpl op body law /\source_zfr_provable M law.
Proof.
 intros BN BT BH BC HAN HChild HOne HZero HPN HEN HAN0 HPA HAE HAn HCoverageBody HCoverage
  HExt HExpectedHead HExpectedTarget.
 assert(PA:p<>a)by(exact(fun E=>@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)p a HPA E)).
 assert(AE:a<>e)by(exact(fun E=>@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)a e HAE E)).
 assert(PE:p<>e)by(exact(fun E=>@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)p e(coding_lt_trans M p a e HPA HAE)E)).
 assert(P0:zeroM M<>p)by(intro E;subst p;contradiction).
 assert(P1:code_numeral M 1<>p)by(intro E;subst p;contradiction).
 assert(A0:zeroM M<>a)by(intro E;subst a;contradiction).
 assert(A1:code_numeral M 1<>a)by(intro E;subst a;contradiction).
 assert(E0:zeroM M<>e)by(intro E;subst e;contradiction).
 assert(E1:code_numeral M 1<>e)by(intro E;subst e;contradiction).
 assert(EChild:e<>child)by(intro E;subst e;contradiction).
 assert(AChild:a<>child)by(intro E;subst a;contradiction).
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 4)projection_operation4)
  (projection_five_values an child(code_numeral M 1)(zeroM M)p))as(op&HOp).
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 3)projection_inner3)
  (projection_three_values a child p))as(projinner&HInner).
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 3)projection_PJ3)
  (projection_three_values child(code_numeral M 1)p))as(profile&HProfile).
 destruct(code_relation_total M source_projection_extension_expression(projection_two_values p a))as(exextension&HExExt).
 destruct(sf_relation_total M SFMember e child)as(childmember&HChildMember).
 destruct(sf_relation_total M SFMember a(code_numeral M 1))as(valuemember&HValueMember).
 destruct(sf_relation_total M SFMember p(zeroM M))as(inResult&HInResult).
 destruct(sf_relation_total M SFAnd named extension)as(previouspair&HPreviousPair).
 destruct(source_named_quantifier_total M false p previouspair)as(exprevious&HExPrevious).
 destruct(source_iff_total M childmember theta)as(childiff&HChildIff).
 destruct(sf_relation_total M SFImpl exprevious childiff)as(localbody&HLocalBody).
 destruct(source_named_quantifier_total M true e localbody)as(allchild&HAllChild).
 destruct(sf_relation_total M SFImpl valuemember allchild)as(headbody&HHeadBody).
 destruct(source_named_quantifier_total M true a headbody)as(generatedhead&HGeneratedHead).
 destruct(sf_relation_total M SFImpl extension childiff)as(extbody&HExtBody).
 destruct(source_named_quantifier_total M true e extbody)as(allpoint&HAllPoint).
 destruct(sf_relation_total M SFAnd childmember extension)as(projectionpair&HProjectionPair).
 destruct(sf_relation_total M SFAnd valuemember projinner)as(left&HLeft).
 destruct(sf_relation_total M SFAnd valuemember theta)as(right&HRight).
 destruct(source_named_quantifier_total M false a right)as(targetex&HTargetEx).
 destruct(source_iff_total M projinner theta)as(guardiff&HGuardIff).
 destruct(sf_relation_total M SFImpl valuemember guardiff)as(guardbody&HGuardBody).
 destruct(source_named_quantifier_total M true a guardbody)as(allguard&HAllGuard).
 destruct(source_iff_total M inResult targetex)as(parentiff&HParentIff).
 destruct(sf_relation_total M SFImpl named parentiff)as(parentbody&HParentBody).
 destruct(source_named_quantifier_total M true p parentbody)as(generatedtarget&HGeneratedTarget).
 assert(BOp:source_bounded M op k).
 { apply(source_parameter_graph_bounded M 4 projection_operation4 projection_operation_bound(source_finite_parameter_names 4)
   (projection_five_values an child(code_numeral M 1)(zeroM M)p)k);[|exact HOp].
   intros[|[|[|[|i]]]]v HI HV;try lia.
   - change(v=an)in HV. now subst v.
   - change(v=child)in HV. now subst v.
   - change(v=code_numeral M 1)in HV. now subst v.
   - change(v=zeroM M)in HV. now subst v. }
 destruct(source_finite_names_bound M[p;e;a])as(ke&BNames).
 assert(BExt:source_bounded M extension ke).
 { apply(source_parameter_graph_bounded M 3 source_def_extension021 source_def_extension_bound source_three_parameter_names
   (environment_extension_names M p e a)ke);[|exact HExt].
   intros[|[|[|i]]]v HI HV;try lia.
   - change(v=p)in HV. subst v. exact(BNames p(or_introl eq_refl)).
   - change(v=e)in HV. subst v. exact(BNames e(or_intror(or_introl eq_refl))).
   - change(v=a)in HV. subst v. exact(BNames a(or_intror(or_intror(or_introl eq_refl)))). }
 destruct(source_member_bounded_exists M e child childmember HChildMember)as(kc&BChildMember).
 destruct(source_member_bounded_exists M a(code_numeral M 1)valuemember HValueMember)as(ka&BValueMember).
 destruct(source_member_bounded_exists M p an inAn HAn)as(kn&BInAn).
 destruct(source_member_bounded_exists M p(zeroM M)inResult HInResult)as(kr&BInResult).
 destruct(source_finite_formulas_bound M[named;theta;head;coverage;op;extension;childmember;valuemember;inAn;inResult]
  ltac:(intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];eexists;eassumption))as(bound&BBase).
 assert(BN':source_bounded M named bound)by(apply BBase;cbn;auto 12).
 assert(BT':source_bounded M theta bound)by(apply BBase;cbn;auto 12).
 assert(BE':source_bounded M extension bound)by(apply BBase;cbn;auto 12).
 assert(BCM:source_bounded M childmember bound)by(apply BBase;cbn;auto 12).
 assert(BVM:source_bounded M valuemember bound)by(apply BBase;cbn;auto 12).
 assert(BIR:source_bounded M inResult bound)by(apply BBase;cbn;auto 12).
 assert(BBin:forall h u v out,sf_binary h ->sf_relation M h u v out ->source_bounded M u bound ->source_bounded M v bound ->source_bounded M out bound).
 { intros h u v out HH HO BU BV. exact(proj2(source_bounded_accept_binary M h u v out bound HH HO)(conj BU BV)). }
 assert(BPrevious:source_bounded M previouspair bound)by(exact(BBin SFAnd named extension previouspair(or_introl eq_refl)HPreviousPair BN' BE')).
 pose proof(source_named_quantifier_bound M false p previouspair exprevious bound BPrevious HExPrevious)as BExPrevious.
 pose proof(source_iff_bounded M childmember theta childiff bound BCM BT' HChildIff)as BChildIff.
 assert(BLocal:source_bounded M localbody bound)by(exact(BBin SFImpl exprevious childiff localbody(or_intror(or_intror eq_refl))HLocalBody BExPrevious BChildIff)).
 pose proof(source_named_quantifier_bound M true e localbody allchild bound BLocal HAllChild)as BAllChild.
 assert(BHeadBody:source_bounded M headbody bound)by(exact(BBin SFImpl valuemember allchild headbody(or_intror(or_intror eq_refl))HHeadBody BVM BAllChild)).
 assert(BExtBody:source_bounded M extbody bound)by(exact(BBin SFImpl extension childiff extbody(or_intror(or_intror eq_refl))HExtBody BE' BChildIff)).
 pose proof(source_named_quantifier_bound M true e extbody allpoint bound BExtBody HAllPoint)as BAllPoint.
 assert(BProjectionPair:source_bounded M projectionpair bound)by(exact(BBin SFAnd childmember extension projectionpair(or_introl eq_refl)HProjectionPair BCM BE')).
 pose proof(source_projection_inner_named_exists M a child p e extension childmember projectionpair projinner
  (fun E=>AE(eq_sym E))EChild(fun E=>PE(eq_sym E))HExt HChildMember HProjectionPair HInner)as HExInner.
 pose proof(source_named_quantifier_bound M false e projectionpair projinner bound BProjectionPair HExInner)as BInner.
 assert(BLeft:source_bounded M left bound)by(exact(BBin SFAnd valuemember projinner left(or_introl eq_refl)HLeft BVM BInner)).
 pose proof(source_projection_outer_named_exists M child(code_numeral M 1)p a projinner valuemember left profile
  AChild(fun E=>A1(eq_sym E))(fun E=>PA(eq_sym E))HInner HValueMember HLeft HProfile)as HExProfile.
 pose proof(source_named_quantifier_bound M false a left profile bound BLeft HExProfile)as BProfile.
 pose proof(source_projection_extension_named_exists M p a e extension exextension(fun E=>PE(eq_sym E))(fun E=>AE(eq_sym E))HExt HExExt)as HExists.
 pose proof(source_named_quantifier_bound M false e extension exextension bound BE' HExists)as BExExtension.
 assert(BRight:source_bounded M right bound)by(exact(BBin SFAnd valuemember theta right(or_introl eq_refl)HRight BVM BT')).
 pose proof(source_named_quantifier_bound M false a right targetex bound BRight HTargetEx)as BTargetEx.
 pose proof(source_iff_bounded M projinner theta guardiff bound BInner BT' HGuardIff)as BGuardIff.
 assert(BGuardBody:source_bounded M guardbody bound)by(exact(BBin SFImpl valuemember guardiff guardbody(or_intror(or_intror eq_refl))HGuardBody BVM BGuardIff)).
 pose proof(source_named_quantifier_bound M true a guardbody allguard bound BGuardBody HAllGuard)as BAllGuard.
 pose proof(source_iff_bounded M inResult targetex parentiff bound BIR BTargetEx HParentIff)as BParentIff.
 assert(BParentBody:source_bounded M parentbody bound)by(exact(BBin SFImpl named parentiff parentbody(or_intror(or_intror eq_refl))HParentBody BN' BParentIff)).
 pose proof(source_named_quantifier_bound M true p parentbody generatedtarget bound BParentBody HGeneratedTarget)as BTarget.
 set(holes:=projection_child_holes M named extension theta).
 assert(BHoles:forall i,exists l,source_bounded M(holes i)l).
 { intros[|[|i]];eexists;eassumption. }
 assert(HHeadEval:source_hole_named_evaluation M(projection_child_names M a e p child)holes projection_child_template generatedhead).
 { pose proof HExPrevious as(pb&pc&pp&PM&PR&PQ). pose proof HAllChild as(eb&ec&ee&EM&ER&EQ).
   pose proof HGeneratedHead as(ab&ac&aa&AM&AR&AQ).
   destruct(source_iff_parts M childmember theta childiff HChildIff)as(lr&rl&HLR&HRL&HAnd).
   unfold projection_child_template,NNTIff. cbn[source_hole_named_evaluation].
   exists a,headbody,ab,ac,aa. split;[reflexivity|]. split;[|exact(conj AM(conj AR AQ))].
   exists valuemember,allchild. split;[|split;[|exact HHeadBody]].
   - exists a,(code_numeral M 1). exact(conj eq_refl(conj eq_refl HValueMember)).
   - exists e,localbody,eb,ec,ee. split;[reflexivity|]. split;[|exact(conj EM(conj ER EQ))].
     exists exprevious,childiff. split;[|split;[|exact HLocalBody]].
     + exists p,previouspair,pb,pc,pp. split;[reflexivity|]. split;[|exact(conj PM(conj PR PQ))].
       exists named,extension. exact(conj eq_refl(conj eq_refl HPreviousPair)).
     + exists lr,rl. split;[|split;[|exact HAnd]].
       * exists childmember,theta. split;[|exact(conj eq_refl HLR)]. exists e,child. exact(conj eq_refl(conj eq_refl HChildMember)).
       * exists theta,childmember. split;[reflexivity|]. split;[|exact HRL]. exists e,child. exact(conj eq_refl(conj eq_refl HChildMember)). }

 pose proof(source_hole_named_scope_empty_exact M(projection_child_names M a e p child)holes projection_child_template generatedhead BHoles HHeadEval)as HGHead.
 pose proof(source_hole_named_scope_empty_exact M(projection_child_names M a e p child)holes projection_child_template head BHoles HExpectedHead)as HEHead.
 assert(EHead:generatedhead=head)by(exact(scoped_source_hole_evaluation_functional M _ _ _ [] _ _ HGHead HEHead)). subst generatedhead.
 set(pholes:=projection_parent_holes M named theta).
 assert(BPHoles:forall i,exists l,source_bounded M(pholes i)l).
 { intros[|i];eexists;eassumption. }
 assert(HTargetEval:source_hole_named_evaluation M(existential_point_names M p a)pholes existential_point_template generatedtarget).
 { pose proof HTargetEx as(ab&ac&aa&AM&AR&AQ). pose proof HGeneratedTarget as(pb&pc&pp&PM&PR&PQ).
   destruct(source_iff_parts M inResult targetex parentiff HParentIff)as(lr&rl&HLR&HRL&HAnd).
   unfold existential_point_template,NNTIff. cbn[source_hole_named_evaluation].
   exists p,parentbody,pb,pc,pp. split;[reflexivity|]. split;[|exact(conj PM(conj PR PQ))].
   exists named,parentiff. split;[reflexivity|]. split;[|exact HParentBody].
   assert(HM:source_hole_named_evaluation M(existential_point_names M p a)pholes(NNTAtom false(CEvar 0)(CEconst 0))inResult).
   { exists p,(zeroM M). exact(conj eq_refl(conj eq_refl HInResult)). }
   assert(HX:source_hole_named_evaluation M(existential_point_names M p a)pholes
     (NNTEx(CEvar 1)(NNTAnd(NNTAtom false(CEvar 1)(CEconst 1))(NNTHole 1)))targetex).
   { exists a,right,ab,ac,aa. split;[reflexivity|]. split;[|exact(conj AM(conj AR AQ))].
     exists valuemember,theta. split;[|exact(conj eq_refl HRight)].
     exists a,(code_numeral M 1). exact(conj eq_refl(conj eq_refl HValueMember)). }
   exists lr,rl. split;[|split;[|exact HAnd]].
   - exists inResult,targetex. exact(conj HM(conj HX HLR)).
   - exists targetex,inResult. exact(conj HX(conj HM HRL)). }
 pose proof(source_hole_named_scope_empty_exact M(existential_point_names M p a)pholes existential_point_template generatedtarget BPHoles HTargetEval)as HGTarget.
 pose proof(source_hole_named_scope_empty_exact M(existential_point_names M p a)pholes existential_point_template target BPHoles HExpectedTarget)as HETarget.
 assert(ETarget:generatedtarget=target)by(exact(scoped_source_hole_evaluation_functional M _ _ _ [] _ _ HGTarget HETarget)). subst generatedtarget.
 set(values:=projection_head_values M named theta extension childmember valuemember exprevious allchild head exextension projinner allpoint profile targetex inAn inResult op coverage target allguard).
 assert(BValues:forall i,source_bounded M(values i)bound).
 { intros[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]];cbn[values projection_head_values].
   - exact BN'.
   - exact BE'.
   - exact BCM.
   - exact BT'.
   - exact BVM.
   - exact BExPrevious.
   - exact BAllChild.
   - apply BBase;cbn;auto 12.
   - exact BExExtension.
   - exact BInner.
   - exact BAllPoint.
   - exact BProfile.
   - exact BTargetEx.
   - apply BBase;cbn;auto 12.
   - exact BIR.
   - apply BBase;cbn;auto 12.
   - apply BBase;cbn;auto 12.
   - exact BTarget.
   - exact BAllGuard.
   - apply source_bounded_accept_falsity. }
 assert(HAbove:forall x,~coding_lt M x k ->coding_lt M k(succM M x)).
 { intros x HX. apply coding_lt_succ_cases.
   destruct(@Peano.trichotomy(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)k x)
    as[H|[H|H]];[now left|now right|contradiction]. }
 assert(HFrame:source_projection_head_frame M an child p a e values bound).
 { constructor.
   - exact BValues.
   - exact(fun E=>AE(eq_sym E)).
   - exact EChild.
   - exact(fun E=>PE(eq_sym E)).
   - exact AChild.
   - exact(fun E=>A1(eq_sym E)).
   - exact(fun E=>PA(eq_sym E)).
   - exact HExt.
   - exact HChildMember.
   - exact HValueMember.
   - exact HAn.
   - exact HInResult.
   - exact HOp.
   - exact HInner.
   - exact HProfile.
   - exact HExExt.
   - exists previouspair,headbody,localbody,extbody,projectionpair,guardbody,left,right,coveragebody,parentbody.
     refine(conj _(conj HExPrevious(conj _(conj HGeneratedHead(conj _(conj HAllChild(conj _(conj HAllPoint(conj _(conj _(conj HAllGuard(conj _(conj _(conj HTargetEx(conj _(conj HCoverage(conj _(HGeneratedTarget)))))))))))))))))).
     + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPreviousPair].
     + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HHeadBody].
     + eapply environment_carrier_code_join;[reflexivity| |exact HLocalBody]. exact HChildIff.
     + eapply environment_carrier_code_join;[reflexivity| |exact HExtBody]. exact HChildIff.
     + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HProjectionPair].
     + eapply environment_carrier_code_join;[reflexivity| |exact HGuardBody]. exact HGuardIff.
     + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HLeft].
     + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HRight].
     + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HCoverageBody].
     + eapply environment_carrier_code_join;[reflexivity| |exact HParentBody]. exact HParentIff.
   - repeat split.
     + exact(source_named_vacuous_above_bound M head e k BH(HAbove e HEN)).
     + exact(source_named_member_vacuous M a(code_numeral M 1)valuemember e AE E1 HValueMember).
     + exact(source_named_vacuous_above_bound M named e(succM M p)BN(proj2(coding_lt_succ_cancel M p e)(coding_lt_trans M p a e HPA HAE))).
     + exact(source_named_vacuous_above_bound M theta e(succM M a)BT(proj2(coding_lt_succ_cancel M a e)HAE)).
     + exact(source_named_vacuous_above_bound M head a k BH(HAbove a HAN0)).
     + exact(source_named_vacuous_above_bound M named a(succM M p)BN(proj2(coding_lt_succ_cancel M p a)HPA)).
     + exact(source_named_vacuous_above_bound M op p k BOp(HAbove p HPN)).
     + exact(source_named_vacuous_above_bound M head p k BH(HAbove p HPN)).
     + exact(source_named_quantifier_is_vacuous M true p coveragebody coverage bound
       (BBin SFImpl named inAn coveragebody(or_intror(or_intror eq_refl))HCoverageBody BN'(BValues 13))HCoverage). }
 destruct(sf_relation_total M SFImpl coverage target)as(inner&HFinalInner).
 destruct(sf_relation_total M SFImpl head inner)as(body&HFinalBody).
 destruct(sf_relation_total M SFImpl op body)as(law&HFinalLaw).
 exists op,inner,body,law. refine(conj HOp(conj HFinalInner(conj HFinalBody(conj HFinalLaw _)))).
 apply(source_zfr_projection_head_frame M an child p a e values bound law HFrame).
 unfold EPA_result. eapply environment_carrier_code_join;[reflexivity| |exact HFinalLaw].
 eapply environment_carrier_code_join;[reflexivity| |exact HFinalBody].
 eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HFinalInner].
Qed.
Print Assumptions source_zfr_projection_head_total.

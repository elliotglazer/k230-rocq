(** Construct the actual finite An head proof around an arbitrary internal
    EnvF matrix. All quantifier/eigenname and finite operation obligations
    are discharged; only the displayed syntax and arithmetic bounds enter. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourcePropositionalTemplates SourceDescriptorProvability SourceZFRProvability
 SourceEnvironmentPointSlots SourceEnvironmentHeadProof SourceEnvironmentHeadCalibration SourceEnvironmentCarrierClosure
 SourceEnvironmentExtensionProgram SourceEnvironmentExtensionQuantifiers SourceEnvironmentExtensionScopes
 SourceDefinabilityPrimitives SourceFiniteParameters SourceFiniteParameterProofs SourceParameterGraphs
 SourceFiniteFamilyBounds SourceNamedVacuity SourceNamedQuantifierRules SourceNamedElimination
 SourceRepresentativeRenaming SourceEnvFScopedHole SourceNamedHoleEvaluation NativeKBundle
 SourceNamedScopes SourceNamedScopeBinding NumericalRenaming.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition environment_point_names(M:Model)(oldr p a e:carrier M)i:=match i with
 |0=>oldr|1=>code_numeral M 1|2=>zeroM M|3=>p|4=>a|_=>e end.
Definition environment_head_values(M:Model)op oldmember headmember extension newmember named coverage exenv allenv head i:=match i with
 |0=>op|1=>oldmember|2=>headmember|3=>extension|4=>newmember|5=>named|6=>coverage
 |7=>exenv|8=>allenv|9=>head|_=>zeroM M end.
Theorem source_zfr_environment_head_total M oldr p e a first named coverage member previousbody deep target k:
 source_bounded M first k ->source_bounded M coverage k ->
 coding_lt M oldr k ->coding_lt M(code_numeral M 1)k ->coding_lt M(zeroM M)k ->
 ~coding_lt M p k ->~coding_lt M e k ->~coding_lt M a k ->
 e<>p ->a<>p ->a<>e ->
 source_representative_renaming M p first named ->source_low_parameter_shift M 3 first deep ->
 sf_relation M SFMember p oldr member ->sf_relation M SFImpl named member previousbody ->
 source_named_quantifier M true p previousbody coverage ->
 code_relation M(fun _=>deep)E_environment_head_point target ->
 exists op inner law,
 code_relation M(environment_point_names M oldr p a e)(environment_extension_fixed_slot 0)op /\
 sf_relation M SFImpl coverage target inner /\sf_relation M SFImpl op inner law /\source_zfr_provable M law.
Proof.
 intros BF BC HOld HOne HZero HP HE HA HEP HAP HAE HNamed HDeep HMember HPrevious HCoverage HTarget.
 set(rho:=environment_point_names M oldr p a e).
 destruct(code_relation_total M(environment_extension_fixed_slot 0)rho)as(op&HOp).
 destruct(code_relation_total M(environment_extension_fixed_slot 3)rho)as(extension&HExt).
 destruct(sf_relation_total M SFMember a(code_numeral M 1))as(headmember&HHeadMember).
 destruct(sf_relation_total M SFMember e(zeroM M))as(newmember&HNewMember).
 pose proof(proj1(source_environment_extension_345_graph M rho extension)HExt)as HExt3.
 assert(BOp:source_bounded M op k).
 { exact(source_environment_operation_bound M rho op k HOld HOne HZero HOp). }
 destruct(source_renamed_bounded_exists M first named p p(code_numeral M 1)(zeroM M)k BF HNamed)as(kn&BN).
 destruct(source_finite_names_bound M[p;e;a])as(ke&BL).
 assert(BExt:source_bounded M extension ke).
 { apply(source_parameter_graph_bounded M 3 source_def_extension021 source_def_extension_bound
   source_three_parameter_names(environment_extension_names M p e a)ke);[|exact HExt3].
   intros[|[|[|i]]]v HI HV;try lia.
   - change(v=p)in HV. subst v. exact(BL p(or_introl eq_refl)).
   - change(v=e)in HV. subst v. exact(BL e(or_intror(or_introl eq_refl))).
   - change(v=a)in HV. subst v. exact(BL a(or_intror(or_intror(or_introl eq_refl)))). }
 destruct(source_member_bounded_exists M p oldr member HMember)as(km&BM).
 destruct(source_member_bounded_exists M a(code_numeral M 1)headmember HHeadMember)as(kh&BH).
 destruct(source_member_bounded_exists M e(zeroM M)newmember HNewMember)as(ko&BO).
 destruct(source_finite_formulas_bound M[op;member;headmember;extension;newmember;named;coverage]
  ltac:(intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];eexists;eassumption))as(bound&BB).
 set(base:=environment_head_values M op member headmember extension newmember named coverage(zeroM M)(zeroM M)(zeroM M)).
 assert(BBase:forall i,source_bounded M(base i)bound).
 { intros[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]];cbn[base environment_head_values];try apply source_bounded_accept_falsity;
   apply BB;cbn;auto 10. }
 destruct(sf_relation_total M SFAnd named extension)as(newbody&HNew).
 assert(BNew:source_bounded M newbody bound).
 { apply(proj2(source_bounded_accept_binary M SFAnd named extension newbody bound(or_introl eq_refl)HNew)).
   split;[exact(BBase 5)|exact(BBase 3)]. }
 destruct(source_named_quantifier_total M false p newbody)as(exenv&HEx).
 pose proof(source_named_quantifier_bound M false p newbody exenv bound BNew HEx)as BEx.
 destruct(sf_relation_total M SFImpl exenv newmember)as(localbody&HLocal).
 assert(BLocal:source_bounded M localbody bound).
 { apply(proj2(source_bounded_accept_binary M SFImpl exenv newmember localbody bound(or_intror(or_intror eq_refl))HLocal)).
   exact(conj BEx(BBase 4)). }
 destruct(source_named_quantifier_total M true e localbody)as(allenv&HAllEnv).
 pose proof(source_named_quantifier_bound M true e localbody allenv bound BLocal HAllEnv)as BAllEnv.
 destruct(sf_relation_total M SFImpl headmember allenv)as(headbody&HHead).
 assert(BHead:source_bounded M headbody bound).
 { apply(proj2(source_bounded_accept_binary M SFImpl headmember allenv headbody bound(or_intror(or_intror eq_refl))HHead)).
   exact(conj(BBase 2)BAllEnv). }
 destruct(source_named_quantifier_total M true a headbody)as(head&HAllHead).
 pose proof(source_named_quantifier_bound M true a headbody head bound BHead HAllHead)as BAllHead.
 set(values:=environment_head_values M op member headmember extension newmember named coverage exenv allenv head).
 assert(BValues:forall i,source_bounded M(values i)bound).
 { intros[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]];cbn[values environment_head_values];try apply source_bounded_accept_falsity;
   try exact BEx;try exact BAllEnv;try exact BAllHead;apply BB;cbn;auto 10. }
 assert(HSlots:forall i,(i<5)%nat ->code_relation M rho(environment_extension_fixed_slot i)(values i)).
 { intros[|[|[|[|[|i]]]]]HI;try lia;cbn[values environment_head_values].
   - exact HOp.
   - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HMember].
   - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HHeadMember].
   - exact HExt.
   - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HNewMember]. }
 assert(GPrevious:code_relation M values(source_prop_expression(SPTImpl(SPTSlot 5)(SPTSlot 1)))previousbody).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPrevious]. }
 assert(GNew:code_relation M values(source_prop_expression(SPTAnd(SPTSlot 5)(SPTSlot 3)))newbody).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HNew]. }
 assert(GLocal:code_relation M values(source_prop_expression environment_extension_local_body)localbody).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HLocal]. }
 assert(GHead:code_relation M values(source_prop_expression environment_extension_head_body)headbody).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HHead]. }
 assert(HAbove:forall x,~coding_lt M x k ->coding_lt M k(succM M x)).
 { intros x HX. apply coding_lt_succ_cases.
   destruct(@Peano.trichotomy(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)k x)
    as[H|[H|H]];[now left|now right|contradiction]. }
 assert(VOp:forall x,~coding_lt M x k ->source_named_vacuous M x op).
 { intros x HX. exact(source_named_vacuous_above_bound M op x k BOp(HAbove x HX)). }
 assert(VCoverage:forall x,~coding_lt M x k ->source_named_vacuous M x coverage).
 { intros x HX. exact(source_named_vacuous_above_bound M coverage x k BC(HAbove x HX)). }
 assert(P0:zeroM M<>p)by(intro E;subst p;contradiction).
 assert(P1:code_numeral M 1<>p)by(intro E;subst p;contradiction).
 assert(E0:zeroM M<>e)by(intro E;subst e;contradiction).
 assert(E1:code_numeral M 1<>e)by(intro E;subst e;contradiction).
 assert(A0:zeroM M<>a)by(intro E;subst a;contradiction).
 assert(A1:code_numeral M 1<>a)by(intro E;subst a;contradiction).
 set(holes:=fun i=>match i with 0=>named|_=>extension end).
 assert(BHoles:forall i,exists l,source_bounded M(holes i)l).
 { intros[|i];[exists kn;exact BN|exists ke;exact BExt]. }
 assert(HNamedEval:source_hole_named_evaluation M(environment_head_names M a e p)holes environment_head_template head).
 { pose proof HEx as(px&pc&pb&PM&PR&PQ).
   pose proof HAllEnv as(ex&ec&eb&EM&ER&EQ).
   pose proof HAllHead as(ax&ac&ab&AM&AR&AQ).
   unfold environment_head_template. cbn[source_hole_named_evaluation].
   exists a,headbody,ax,ac,ab. split;[reflexivity|]. split;[|exact(conj AM(conj AR AQ))].
   exists headmember,allenv. split;[|split;[|exact HHead]].
   - exists a,(code_numeral M 1). exact(conj eq_refl(conj eq_refl HHeadMember)).
   - exists e,localbody,ex,ec,eb. split;[reflexivity|]. split;[|exact(conj EM(conj ER EQ))].
     exists exenv,newmember. split;[|split;[|exact HLocal]].
     + exists p,newbody,px,pc,pb. split;[reflexivity|]. split;[|exact(conj PM(conj PR PQ))].
       exists named,extension. exact(conj eq_refl(conj eq_refl HNew)).
     + exists e,(zeroM M). exact(conj eq_refl(conj eq_refl HNewMember)). }
 assert(HCal:code_relation M(fun _=>deep)E_environment_head_point head).
 { apply(source_environment_head_calibration M a e p holes deep head BHoles A0 A1 E0).
   - exact(source_representative_three_scopes M first named deep p e a k BF HP HE HA HNamed HDeep).
   - exact(source_environment_extension_scoped M p e a extension HEP HAP HAE HExt3).
   - exact HNamedEval. }
 assert(EHead:head=target)by(eapply code_relation_functional;eassumption). subst head.
 destruct(sf_relation_total M SFImpl coverage target)as(inner&HInner).
 destruct(sf_relation_total M SFImpl op inner)as(law&HLaw).
 assert(GLaw:code_relation M values(source_prop_expression environment_extension_all_result)law).
 { eapply environment_carrier_code_join;[reflexivity| |exact HLaw].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HInner]. }
 exists op,inner,law. refine(conj HOp(conj HInner(conj HLaw _))).
 apply(source_zfr_environment_head_proof M rho values p e a previousbody newbody localbody headbody law bound
  BValues HSlots GPrevious GNew GLocal GHead HCoverage HEx HAllEnv HAllHead).
 - exact(VOp p HP).
 - exact(source_named_member_vacuous M a(code_numeral M 1)headmember p HAP P1 HHeadMember).
 - exact(source_named_member_vacuous M e(zeroM M)newmember p HEP P0 HNewMember).
 - exact(VOp e HE).
 - exact(VCoverage e HE).
 - exact(source_named_member_vacuous M a(code_numeral M 1)headmember e HAE E1 HHeadMember).
 - exact(VOp a HA).
 - exact(VCoverage a HA).
 - exact GLaw.
Qed.
Print Assumptions source_zfr_environment_head_total.

(** Actual local projection inference from the child representation head.
    Existential extension is supplied as an ordinary source theorem; every
    logical quantifier step here is constructed directly in the source calculus. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceDescriptorNamedUniversal
 SourceRepresentationDifferenceProgram SourceNamedVacuity SourceNamedQuantifierRules SourceProjectionWitnessEquivalence.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EPH_head_body:=SPTImpl(SPTSlot 4)(SPTSlot 6).
Definition EPH_local_body:=SPTImpl(SPTSlot 5)(SPTIff(SPTSlot 2)(SPTSlot 3)).
Definition EPH_ext_body:=SPTImpl(SPTSlot 1)(SPTIff(SPTSlot 2)(SPTSlot 3)).
Definition EPH_condition:=SPTAnd(SPTSlot 7)(SPTAnd(SPTSlot 4)(SPTSlot 0)).
Definition EPH_point:=SPTImpl EPH_condition EPH_ext_body.
Definition EPH_result:=SPTImpl(SPTSlot 7)(SPTImpl(SPTSlot 4)(SPTImpl(SPTSlot 0)(SPTIff(SPTSlot 9)(SPTSlot 3)))).
Ltac eph_ctx:=apply SPTCtx;cbn;auto 14.
Lemma EPH_point_program:source_prop_program
 [SPTImpl(SPTSlot 7)EPH_head_body;SPTImpl(SPTSlot 6)EPH_local_body;
  SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTSlot 5)]EPH_point.
Proof.
 unfold EPH_point,EPH_condition,EPH_ext_body,EPH_head_body,EPH_local_body.
 do 2 apply SPTII. eapply SPTIE with(a:=SPTSlot 5).
 - eapply SPTIE with(a:=SPTSlot 6);[eph_ctx|]. eapply SPTIE with(a:=SPTSlot 4).
   + eapply SPTIE with(a:=SPTSlot 7);[eph_ctx|]. apply SPTCE1 with(b:=SPTAnd(SPTSlot 4)(SPTSlot 0));eph_ctx.
   + apply SPTCE1 with(b:=SPTSlot 0). apply SPTCE2 with(a:=SPTSlot 7);eph_ctx.
 - eapply SPTIE with(a:=SPTAnd(SPTSlot 0)(SPTSlot 1));[eph_ctx|]. apply SPTCI;[|eph_ctx].
   apply SPTCE2 with(a:=SPTSlot 4). apply SPTCE2 with(a:=SPTSlot 7);eph_ctx.
Qed.
Lemma EPH_result_program:source_prop_program
 [SPTImpl EPH_condition(SPTSlot 10);SPTImpl(SPTSlot 10)(SPTImpl(SPTSlot 8)(SPTIff(SPTSlot 9)(SPTSlot 3)));SPTSlot 8]EPH_result.
Proof.
 unfold EPH_result,EPH_condition. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 8);[|eph_ctx]. eapply SPTIE with(a:=SPTSlot 10);[eph_ctx|].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 7)(SPTAnd(SPTSlot 4)(SPTSlot 0)));[eph_ctx|].
 apply SPTCI;[eph_ctx|apply SPTCI;eph_ctx].
Qed.
Definition projection_witness_values {A}(values:nat->A)i:=match i with
 |0=>values 1|1=>values 2|2=>values 3|3=>values 10|4=>values 8|_=>values 9 end.
Theorem source_descriptor_projection_head_point M T values a e p previouspair headbody localbody extbody projectionpair result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 0)(SPTSlot 1)))previouspair ->
 source_named_quantifier M false p previouspair(values 5) ->
 code_relation M values(source_prop_expression EPH_head_body)headbody ->source_named_quantifier M true a headbody(values 7) ->
 code_relation M values(source_prop_expression EPH_local_body)localbody ->source_named_quantifier M true e localbody(values 6) ->
 code_relation M values(source_prop_expression EPH_ext_body)extbody ->source_named_quantifier M true e extbody(values 10) ->
 source_named_quantifier M false e(values 1)(values 8) ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 2)(SPTSlot 1)))projectionpair ->
 source_named_quantifier M false e projectionpair(values 9) ->
 source_named_vacuous M e(values 7) ->source_named_vacuous M e(values 4) ->
 source_named_vacuous M e(values 0) ->source_named_vacuous M e(values 3) ->
 source_descriptor_provable M T(values 8) ->
 code_relation M values(source_prop_expression EPH_result)result ->source_descriptor_provable M T result.
Proof.
 intros HB HPrevious HExP HHead HAllA HLocal HAllE HExt HAllExt HExExt HPair HExPair VH VA VP VT PExt HResult.
 assert(PHead:source_descriptor_template M T values(SPTImpl(SPTSlot 7)EPH_head_body)).
 { intros f HF. destruct(source_prop_template_binary M values SFImpl(SPTSlot 7)EPH_head_body f HF)as(u&v&HU&HV&HO).
   change(u=values 7)in HU. subst u. rewrite(code_relation_functional M _ values v headbody HV HHead)in HO.
   exact(source_descriptor_named_all_specialization M T a headbody(values 7)f k
    (source_prop_template_bound M values EPH_head_body k HB headbody HHead)HAllA HO). }
 assert(PLocal:source_descriptor_template M T values(SPTImpl(SPTSlot 6)EPH_local_body)).
 { intros f HF. destruct(source_prop_template_binary M values SFImpl(SPTSlot 6)EPH_local_body f HF)as(u&v&HU&HV&HO).
   change(u=values 6)in HU. subst u. rewrite(code_relation_functional M _ values v localbody HV HLocal)in HO.
   exact(source_descriptor_named_all_specialization M T e localbody(values 6)f k
    (source_prop_template_bound M values EPH_local_body k HB localbody HLocal)HAllE HO). }
 assert(PIntro:source_descriptor_template M T values(SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTSlot 5))).
 { exact(source_descriptor_template_named_intro M T values p(SPTAnd(SPTSlot 0)(SPTSlot 1))5 previouspair k
   (source_prop_template_bound M values(SPTAnd(SPTSlot 0)(SPTSlot 1))k HB previouspair HPrevious)HPrevious HExP). }
 assert(PAllExt:source_descriptor_template M T values(SPTImpl EPH_condition(SPTSlot 10))).
 { apply(source_descriptor_template_named_all M T values e EPH_condition EPH_ext_body 10 extbody k HB HExt HAllExt).
   - unfold EPH_condition. cbn[source_prop_named_vacuity]. auto.
   - apply(source_descriptor_template_program M T values k _ _ HB EPH_point_program).
     intros q[<-|[<-|[<-|[]]]];assumption. }
 assert(PW:source_descriptor_template M T values(SPTImpl(SPTSlot 10)(SPTImpl(SPTSlot 8)(SPTIff(SPTSlot 9)(SPTSlot 3))))).
 { intros f HF. apply(source_descriptor_projection_witness_equivalence M T(projection_witness_values values)e extbody projectionpair f k).
   - intros[|[|[|[|[|i]]]]];apply HB.
   - exact HExt.
   - exact HPair.
   - exact HAllExt.
   - exact HExExt.
   - exact HExPair.
   - exact VT.
   - exact HF. }
 exact(source_descriptor_template_program M T values k _ _ HB EPH_result_program
  ltac:(intros q[<-|[<-|[<-|[]]]];try assumption;intros f HF;change(f=values 8)in HF;now subst f)result HResult).
Qed.
Print Assumptions source_descriptor_projection_head_point.

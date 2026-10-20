(** Actual fixed propositional assembly of the lookup successor point.
    Inputs are ordinary source deductions; no rule is supplied as an axiom. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SetCodeDescent
 SourcePropositionalTemplates SourceEnvFLookupFiniteProofs SourceEnvFLookupPrograms SourceWitnessProofComposition SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Ltac el_graph:=lazymatch goal with
 | |-code_relation ?M ?rho(source_prop_expression(SPTSlot ?idx))?out=>reflexivity
 | |-code_relation ?M ?rho(source_prop_expression SPTFalse)?out=>reflexivity
 | |-code_relation ?M ?rho(source_prop_expression(SPTImpl ?A ?B))?out=>
  match goal with H:sf_relation M SFImpl ?a ?b out|-_=>apply(source_prop_template_join M rho SFImpl A B a b out);[el_graph|el_graph|exact H]end
 | |-code_relation ?M ?rho(source_prop_expression(SPTAnd ?A ?B))?out=>
  match goal with H:sf_relation M SFAnd ?a ?b out|-_=>apply(source_prop_template_join M rho SFAnd A B a b out);[el_graph|el_graph|exact H]end
 end.
Local Ltac part M a b f H B:=exact(source_has_bound_binary_parts M SFImpl a b f(or_intror(or_intror eq_refl))H B).
Theorem source_zfr_env_lookup_head_point M E N D X Q Eq R dn domain un unique hr ht head envBody qr er point:
 sf_relation M SFImpl N D dn->sf_relation M SFImpl E dn domain->
 sf_relation M SFImpl N Eq un->sf_relation M SFImpl Q un unique->
 sf_relation M SFImpl Eq R hr->sf_relation M SFImpl X hr ht->sf_relation M SFImpl D ht head->
 sf_relation M SFAnd E X envBody->sf_relation M SFImpl Q R qr->sf_relation M SFImpl envBody qr er->sf_relation M SFImpl N er point->
 source_zfr_provable M domain->source_zfr_provable M unique->source_zfr_provable M head->source_zfr_provable M point.
Proof.
 intros HDN HD HUN HU HHR HHT HH HB HQR HER HP PD PU PH.
 destruct(source_zfr_provable_has_bound M domain PD)as(kd&BD).
 destruct(proj1(source_bounded_accept_binary M SFImpl E dn domain kd(or_intror(or_intror eq_refl))HD)BD)as(BE&BDN).
 destruct(proj1(source_bounded_accept_binary M SFImpl N D dn kd(or_intror(or_intror eq_refl))HDN)BDN)as(BN&BD0).
 destruct(source_zfr_provable_has_bound M unique PU)as(ku&BU).
 destruct(proj1(source_bounded_accept_binary M SFImpl Q un unique ku(or_intror(or_intror eq_refl))HU)BU)as(BQ&BUN).
 destruct(proj1(source_bounded_accept_binary M SFImpl N Eq un ku(or_intror(or_intror eq_refl))HUN)BUN)as(_&BEq).
 destruct(source_zfr_provable_has_bound M head PH)as(kh&BH).
 destruct(proj1(source_bounded_accept_binary M SFImpl D ht head kh(or_intror(or_intror eq_refl))HH)BH)as(_&BHT).
 destruct(proj1(source_bounded_accept_binary M SFImpl X hr ht kh(or_intror(or_intror eq_refl))HHT)BHT)as(BX&BHR).
 destruct(proj1(source_bounded_accept_binary M SFImpl Eq R hr kh(or_intror(or_intror eq_refl))HHR)BHR)as(_&BR).
 apply(source_zfr_prop_pairs_finite M[(el_domain,domain);(el_unique,unique);(el_head,head)]el_point
  source_env_lookup_head_program[E;N;D;X;Q;Eq;R]point).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];eexists;eassumption.
 - intros a f[H|[H|[H|[]]]];inversion H;subst a f;split;[unfold el_domain;el_graph|exact PD|unfold el_unique;el_graph|exact PU|unfold el_head;el_graph|exact PH].
 - unfold el_point;el_graph.
Qed.
Theorem source_zfr_env_lookup_tail_point M E N D X Q Eq R O neg dn domain distn distinct oldn old last ti tt tail envBody qr er point:
 sf_relation M SFImpl Eq(zeroM M)neg->
 sf_relation M SFImpl N D dn->sf_relation M SFImpl E dn domain->
 sf_relation M SFImpl N neg distn->sf_relation M SFImpl Q distn distinct->
 sf_relation M SFImpl Q O oldn->sf_relation M SFImpl E oldn old->
 sf_relation M SFImpl O R last->sf_relation M SFImpl neg last ti->sf_relation M SFImpl X ti tt->sf_relation M SFImpl D tt tail->
 sf_relation M SFAnd E X envBody->sf_relation M SFImpl Q R qr->sf_relation M SFImpl envBody qr er->sf_relation M SFImpl N er point->
 source_zfr_provable M domain->source_zfr_provable M distinct->source_zfr_provable M old->source_zfr_provable M tail->source_zfr_provable M point.
Proof.
 intros HNeg HDN HD HDisN HDis HOldN HOld HL HTI HTT HT HB HQR HER HP PD PDis PO PT.
 destruct(source_zfr_provable_has_bound M domain PD)as(kd&BD).
 destruct(proj1(source_bounded_accept_binary M SFImpl E dn domain kd(or_intror(or_intror eq_refl))HD)BD)as(BE&BDN).
 destruct(proj1(source_bounded_accept_binary M SFImpl N D dn kd(or_intror(or_intror eq_refl))HDN)BDN)as(BN&BD0).
 destruct(source_zfr_provable_has_bound M distinct PDis)as(ku&BU).
 destruct(proj1(source_bounded_accept_binary M SFImpl Q distn distinct ku(or_intror(or_intror eq_refl))HDis)BU)as(BQ&BDistN).
 destruct(proj1(source_bounded_accept_binary M SFImpl N neg distn ku(or_intror(or_intror eq_refl))HDisN)BDistN)as(_&BNeg).
 destruct(proj1(source_bounded_accept_binary M SFImpl Eq(zeroM M)neg ku(or_intror(or_intror eq_refl))HNeg)BNeg)as(BEq&_).
 destruct(source_zfr_provable_has_bound M tail PT)as(kt&BT).
 destruct(proj1(source_bounded_accept_binary M SFImpl D tt tail kt(or_intror(or_intror eq_refl))HT)BT)as(_&BTT).
 destruct(proj1(source_bounded_accept_binary M SFImpl X ti tt kt(or_intror(or_intror eq_refl))HTT)BTT)as(BX&BTI).
 destruct(proj1(source_bounded_accept_binary M SFImpl neg last ti kt(or_intror(or_intror eq_refl))HTI)BTI)as(_&BL).
 destruct(proj1(source_bounded_accept_binary M SFImpl O R last kt(or_intror(or_intror eq_refl))HL)BL)as(BO&BR).
 apply(source_zfr_prop_pairs_finite M[(el_domain,domain);(el_distinct,distinct);(el_old,old);(el_tail,tail)]el_point
  source_env_lookup_tail_program[E;N;D;X;Q;Eq;R;O]point).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];eexists;eassumption.
 - intros a f[H|[H|[H|[H|[]]]]];inversion H;subst a f;split;[unfold el_domain;el_graph|exact PD|unfold el_distinct;el_graph|exact PDis|unfold el_old;el_graph|exact PO|unfold el_tail;el_graph|exact PT].
 - unfold el_point;el_graph.
Qed.
Print Assumptions source_zfr_env_lookup_head_point.
Print Assumptions source_zfr_env_lookup_tail_point.

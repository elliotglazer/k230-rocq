(** Introduce the genuine RR carrier into the existential conclusion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionStructureInputs SourceRecursionRangeChart SourceRecursionClosureSyntax
 SourceRecursionClosureExists SourceRecursionClosureFromStructure SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_carrier_exists M phi o a N Y A chart target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->
 source_rec_structure_inputs M phi o N A ->source_rec_range_chart M phi o a N Y chart ->source_rec_closure_exists M phi a target ->
 source_finite_telescope M(A++[chart])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BY HA HChart HTarget HLaw.
 pose proof(source_rec_structure_inputs_bounded M phi o N A k BP BO BN HA)as Bounds.
 pose proof(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HChart)as BChart.
 pose proof(source_rec_closure_exists_bounded M phi a target k BP BA HTarget)as BTarget.
 destruct(source_rec_closure_total M phi a Y)as(body&HBody).
 destruct(source_finite_telescope_total M(A++[chart])body)as(bodyLaw&HBodyLaw).
 pose proof(source_zfr_rec_closure_from_structure M phi o a N Y A chart body bodyLaw k BP BO BA BN BY HA HChart HBody HBodyLaw)as PBodyLaw.
 apply(source_zfr_finite_rule M[bodyLaw](A++[chart])target law k).
 - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BChart].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact PBodyLaw.
 - intros cb cc cn BC Laws Premises.
   assert(PBody:source_full_prv M cb cc cn body).
   { apply(source_full_finite_telescope_apply M(A++[chart])body bodyLaw HBodyLaw cb cc cn);[apply Laws;now left|exact Premises]. }
   exact(source_full_rec_closure_exists_intro M cb cc cn phi a Y body target k BP BA BC HBody HTarget PBody).
Qed.
Print Assumptions source_zfr_rec_carrier_exists.

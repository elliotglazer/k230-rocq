(** A chosen initial attempt places its initial value in the actual RR range. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionRangeRelation SourceRecursionRangeIntroduction SourceRecursionRangeFibre SourceRecursionRangeChart SourceRecursionRangeChartRules SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_range_base_chosen M phi o a N f Y member chart att app target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M Y k ->
 sf_relation M SFMember o N member ->source_rec_range_chart M phi o a N Y chart ->source_rec_attempt M phi o a N f att ->source_rec_app M f o a app ->sf_relation M SFMember a Y target ->
 source_finite_telescope M[member;chart;att;app]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BY HM HC HT HA HTarget HLaw.
 pose proof(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN))as BM.
 pose proof(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HC)as BC.
 pose proof(source_rec_attempt_bounded M phi o a N f att k BP BO BA BN BF HT)as BT.
 pose proof(source_rec_app_bounded M f o a app k BF BO BA HA)as BA'.
 pose proof(proj2(source_bounded_accept_atom M SFMember a Y target k(or_introl eq_refl)HTarget)(conj BA BY))as BTarget.
 apply(source_zfr_finite_rule M[][member;chart;att;app]target law k).
 - intros x[<-|[<-|[<-|[<-|[]]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x HX. contradiction.
 - intros cb cc cn BContext Laws Premises.
   destruct(source_rec_rr_total M phi o a o a N)as(rr&HR).
   assert(PR:source_full_prv M cb cc cn rr).
   { apply(source_full_rec_rr_intro M cb cc cn phi o a o a N rr f member att app k BP BO BA BO BA BN BContext HR HM HT HA);
     apply Premises;cbn;tauto. }
   destruct(source_rec_range_fibre_total M phi o a N a)as(fibre&HF).
   pose proof(source_full_rec_range_fibre_intro M cb cc cn phi o a N a o member rr fibre k BP BO BA BN BA BContext HM HR HF(Premises member ltac:(cbn;tauto))PR)as PF.
   exact(source_full_rec_range_chart_in M cb cc cn phi o a N Y a chart target fibre BP HC HTarget HF(Premises chart ltac:(cbn;tauto))PF).
Qed.
Print Assumptions source_zfr_rec_range_base_chosen.

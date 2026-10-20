(** Actual chosen-successor branch of the K-closure proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalInstantiation SourceConjunctionRules SourceFiniteTelescope SourceZFRFiniteRule
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourceOrdinalPredicate SourceRecursionBinaryInstance
 SourceReflectionRecursionKernel SourceReflectionStep SourceReflectionOrdinalChartRules SourceReflectionKFInputs
 SourceReflectionKFNext SourceReflectionKFWitness SourceReflectionKFChosen SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_reflection_KF_branch M level sb sc count phi a Y K x w A binary memberY body target law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->source_bounded M phi(code_numeral M 2) ->
 source_reflection_step M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi ->
 coding_lt M a k ->coding_lt M Y k ->coding_lt M K k ->coding_lt M x k ->coding_lt M w k ->
 source_reflection_KF_inputs M phi a Y K x A ->source_rec_binary M phi x w binary ->sf_relation M SFMember w Y memberY ->sf_relation M SFAnd binary memberY body ->
 source_reflection_KF_next M(source_L_domain_code M)level sb sc count K x target ->source_finite_telescope M(A++[body])target law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BP HMatrix BA BY BK BX BW HA HB HMY HBody HT HLaw.
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_KF_inputs_bounded M phi a Y K x A k BP BA BY BK BX HA)as Bounds.
 pose proof(source_rec_binary_bounded M phi x w binary k BP BX BW HB)as BB.
 pose proof(proj2(source_bounded_accept_atom M SFMember w Y memberY k(or_introl eq_refl)HMY)(conj BW BY))as BMY.
 pose proof(proj2(source_bounded_accept_binary M SFAnd binary memberY body k(or_introl eq_refl)HBody)(conj BB BMY))as BBody.
 pose proof(source_reflection_KF_next_bounded M(source_L_domain_code M)level sb sc count K x target k(numerical_L_domain_bounded M)HL HV BK BX HT)as BT.
 pose proof HA as HInputs. destruct HA as(chart&closure&memberK&E&HC&HClosure&HMK). subst A.
 apply(source_zfr_finite_rule M[][chart;closure;memberK;body]target law k).
 - intros f HF. destruct HF as[<-|[<-|[<-|[<-|[]]]]];[apply Bounds;now left|apply Bounds;right;now left|apply Bounds;right;right;now left|exact BBody].
 - exact BT.
 - exact HLaw.
 - intros f HF. contradiction.
 - intros b c n BC Laws Premises.
   pose proof(Premises body ltac:(cbn;tauto))as PBody.
   pose proof(source_full_conjunction_left M b c n binary memberY body HBody PBody)as PB.
   pose proof(source_full_conjunction_right M b c n binary memberY body HBody PBody)as PMY.
   destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)x)as(ordinal&HO).
   destruct(sf_relation_total M SFMember x Y)as(memberXY&HXY).
   destruct(source_full_reflection_ordinal_chart_out M b c n Y K chart x memberK memberXY ordinal HC HMK HXY HO
    (Premises chart ltac:(cbn;tauto))(Premises memberK ltac:(cbn;tauto)))as(_&PO).
   pose proof(source_reflection_rec_binary M(source_L_domain_code M)level sb sc count phi x w binary(numerical_L_domain_bounded M)HL HV HMatrix HB)as HStep.
   destruct(source_reflection_KF_witness_total M(source_L_domain_code M)level sb sc count K x w)as(witness&HW).
   pose proof(source_full_reflection_KF_chosen M b c n(source_L_domain_code M)level sb sc count Y K x w chart binary ordinal memberY witness
    HC HStep HO HMY HW(Premises chart ltac:(cbn;tauto))PB PO PMY)as PW.
   exact(source_full_reflection_KF_next_intro M b c n(source_L_domain_code M)level sb sc count K x w witness target k
    (numerical_L_domain_bounded M)HL HV BK BX BC HW HT PW).
Qed.
Print Assumptions source_zfr_reflection_KF_branch.

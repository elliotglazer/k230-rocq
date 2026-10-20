(** Discharge the final value variable by actual source AllI. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceRecursionNextIn
 SourceRecursionClosureCarrierInputs SourceRecursionClosureFibre SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_values_closed M phi Y out:=exists guard next point,
 sf_relation M SFMember(zeroM M)(succM M Y)guard /\source_rec_next_in M phi(zeroM M)(succM M Y)next /\
 sf_relation M SFImpl guard next point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_rec_values_closed_total M phi Y:exists out,source_rec_values_closed M phi Y out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M Y))as(guard&HG).
 destruct(source_rec_next_in_total M phi(zeroM M)(succM M Y))as(next&HN).
 destruct(sf_relation_total M SFImpl guard next)as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO). exists out,guard,next,point. auto.
Qed.
Theorem source_rec_values_closed_bounded M phi Y out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M Y k ->source_rec_values_closed M phi Y out ->source_bounded M out k.
Proof.
 intros BP BY(guard&next&point&HG&HN&HP&HO).
 pose proof(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M Y)guard(succM M k)(or_introl eq_refl)HG)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M Y k)BY)))as BG.
 pose proof(source_rec_next_in_bounded M phi(zeroM M)(succM M Y)next(succM M k)BP(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M Y k)BY)HN)as BN.
 exact(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HO)
  (proj2(source_bounded_accept_binary M SFImpl guard next point(succM M k)(or_intror(or_intror eq_refl))HP)(conj BG BN))).
Qed.
Theorem source_zfr_rec_range_closed M phi o a N Y A closed law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->
 source_rec_closure_carrier_inputs M phi o a N Y A ->source_rec_values_closed M phi Y closed ->
 source_finite_telescope M A closed law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BY HA HC HLaw. set(s:=succM M).
 pose proof(source_rec_closure_carrier_inputs_bounded M phi o a N Y A k BP BO BA BN BY HA)as Bounds.
 pose proof(source_rec_values_closed_bounded M phi Y closed k BP BY HC)as BClosed.
 destruct HC as(guard&next&point&HG&HN&HP&HAll).
 pose proof(proj1(source_bounded_accept_unary M SFAll point closed k(or_introl eq_refl)HAll)BClosed)as BPoint.
 destruct(source_rec_closure_carrier_inputs_total M phi(s o)(s a)(s N)(s Y))as(AS&HAS).
 pose proof(source_rec_closure_carrier_inputs_shift M phi o a N Y A AS BP HA HAS)as HS.
 destruct(source_finite_telescope_total M AS point)as(pointLaw&HPointLaw).
 assert(HPointTel:source_finite_telescope M(AS++[guard])next pointLaw).
 { apply(source_finite_telescope_prefix M AS[guard]point next pointLaw HPointLaw). exists next. split;[reflexivity|exact HP]. }
 pose proof(source_zfr_rec_closure_member M phi(s o)(s a)(s N)(zeroM M)(s Y)AS guard next pointLaw(s k)BP
  ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HAS HG HN HPointTel)as PPoint.
 exact(source_zfr_finite_telescope_all M A AS point closed pointLaw law k Bounds BPoint HS HAll HPointLaw HLaw PPoint).
Qed.
Print Assumptions source_rec_values_closed_total.
Print Assumptions source_rec_values_closed_bounded.
Print Assumptions source_zfr_rec_range_closed.

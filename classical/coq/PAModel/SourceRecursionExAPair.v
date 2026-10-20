(** Eliminate the actual ordered-pair existential in successor ExA. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopeRemoveTheorem
 SourceRecursionSetOperations SourceRecursionPrimitiveShifts SourceRecursionPrimitiveExistence
 SourceRecursionExAStepInputs SourceRecursionExAAdjoin SourceRecursionExistsAttempt SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_exa_from_step_values M phi o a N f z next p w A target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->
 coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->source_rec_exa_step_inputs M phi o a N f z next p w A ->
 source_rec_exa M phi next o a N target ->source_finite_telescope M A target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BNext BP' BW HInputs HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_exa_step_inputs_bounded M phi o a N f z next p w A k BP BO BA BN BF BZ BNext BP' BW HInputs)as Bounds.
 pose proof(source_rec_exa_bounded M phi next o a N target k BP BNext BO BA BN HTarget)as BTarget.
 destruct(source_zfr_rec_ordered_pair_exists M next w)as(body&ex&HBody&HEx&PEx).
 pose proof(source_rec_ordered_pair_bounded M(s next)(s w)(zeroM M)body(s k)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HBody)as BBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx body ex k(or_intror eq_refl)HEx)BBody)as BEx.
 destruct(source_rec_exa_step_inputs_total M phi(s o)(s a)(s N)(s f)(s z)(s next)(s p)(s w))as(AS&HIS).
 pose proof(source_rec_exa_step_inputs_shift M phi o a N f z next p w A AS BP HInputs HIS)as HS.
 destruct(source_rec_exa_total M phi(s next)(s o)(s a)(s N))as(targetS&HTargetS).
 pose proof(source_rec_exa_shift M phi next o a N target targetS BP HTarget HTargetS)as STarget.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 pose proof(source_zfr_rec_exa_with_pair M phi(s o)(s a)(s N)(s f)(s z)(s next)(s p)(s w)(zeroM M)AS body targetS deep(s k)
  BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
  ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HIS HBody HTargetS HDeep)as PDeep.
 destruct(source_finite_telescope_total M(A++[ex])target)as(withEx&HWithEx).
 pose proof(source_zfr_finite_telescope_exists M A AS body ex target targetS deep withEx k Bounds BEx BTarget HS HEx STarget HDeep HWithEx PDeep)as PWithEx.
 exact(source_zfr_finite_telescope_remove_theorem M A ex target withEx law k Bounds BTarget HWithEx HLaw PEx PWithEx).
Qed.
Print Assumptions source_zfr_rec_exa_from_step_values.

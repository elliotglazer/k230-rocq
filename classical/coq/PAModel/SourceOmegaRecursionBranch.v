(** The actual generic recursion kernel consumes the fixed omega body. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone FixedSourceBounds
 NumericalContexts NumericalSourceFull SourceConjunctionRules SourceFiniteTelescope SourceZFRFiniteRule
 SourceRecursionStructureInputs SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionTotalRelation
 SourceRecursionClosureExists SourceRecursionClosureNamedTheorem SourceOmegaRecursionFixed SourceOmegaRecursionShell SourceOmegaRecursionBounds SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque code_numeral source_omega_recursion_body_code.
Theorem source_zfr_rec_omega_branch M phi funlaw totalG target law:
 source_bounded M phi(code_numeral M 2) ->source_rec_functionality M phi funlaw ->source_rec_total_relation M phi totalG ->
 source_rec_closure_exists M phi(code_numeral M 2)target ->
 source_finite_telescope M[funlaw;totalG;source_omega_recursion_body_code M]target law ->source_zfr_provable M law.
Proof.
 intros BP HFun HG HTarget HLaw.
 destruct(source_omega_recursion_body_shell M)as(member&total&injective&nonzero&inductive&tail1&tail2&tail3&HM&HT&HI&HN&HD&H3&H2&H1&H0).
 set(A:=[funlaw;totalG;nonzero;injective;total;inductive;member]).
 assert(HA:source_rec_structure_inputs M phi(code_numeral M 0)(code_numeral M 1)A).
 { exists funlaw,totalG,nonzero,injective,total,inductive,member. split;[reflexivity|]. auto 10. }
 destruct(source_finite_telescope_total M A target)as(kernel&HKernel).
 pose proof(source_zfr_rec_closure_named_theorem M phi(code_numeral M 0)(code_numeral M 2)(code_numeral M 1)A target kernel BP HA HTarget HKernel)as PKernel.
 assert(BClosed:forall f,source_bounded M f(zeroM M)->source_bounded M f(code_numeral M 3)).
 { intros f BF. exact(source_bounded_monotone M f(zeroM M)(code_numeral M 3)BF(coding_zero_lt_succ M(code_numeral M 3))). }
 assert(BFun:source_bounded M funlaw(code_numeral M 3))by(exact(BClosed funlaw(source_rec_functionality_closed M phi funlaw BP HFun))).
 assert(BG:source_bounded M totalG(code_numeral M 3))by(exact(BClosed totalG(source_rec_total_relation_closed M phi totalG BP HG))).
 assert(BBody:source_bounded M(source_omega_recursion_body_code M)(code_numeral M 3)).
 { exact(source_bounded_monotone M _ (code_numeral M 2)(code_numeral M 3)(source_omega_recursion_body_bounded M)(proj2(fixed_source_numeral_lt_iff M 2 4)ltac:(lia))). }
 pose proof(source_rec_closure_exists_bounded M phi(code_numeral M 2)target(code_numeral M 3)BP(proj2(fixed_source_numeral_lt_iff M 2 3)ltac:(lia))HTarget)as BTarget.
 apply(source_zfr_finite_rule M[kernel][funlaw;totalG;source_omega_recursion_body_code M]target law(code_numeral M 3)).
 - intros x[<-|[<-|[<-|[]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact PKernel.
 - intros cb cc cn BC Laws Premises.
   pose proof(Premises(source_omega_recursion_body_code M)ltac:(cbn;tauto))as PBody.
   pose proof(source_full_conjunction_left M cb cc cn member tail1 _ H0 PBody)as PMember.
   pose proof(source_full_conjunction_right M cb cc cn member tail1 _ H0 PBody)as PTail1.
   pose proof(source_full_conjunction_left M cb cc cn total tail2 tail1 H1 PTail1)as PTotal.
   pose proof(source_full_conjunction_right M cb cc cn total tail2 tail1 H1 PTail1)as PTail2.
   pose proof(source_full_conjunction_left M cb cc cn injective tail3 tail2 H2 PTail2)as PInjective.
   pose proof(source_full_conjunction_right M cb cc cn injective tail3 tail2 H2 PTail2)as PTail3.
   pose proof(source_full_conjunction_left M cb cc cn nonzero inductive tail3 H3 PTail3)as PNonzero.
   pose proof(source_full_conjunction_right M cb cc cn nonzero inductive tail3 H3 PTail3)as PInductive.
   apply(source_full_finite_telescope_apply M A target kernel HKernel cb cc cn(Laws kernel(or_introl eq_refl))).
   intros x HX. unfold A in HX. destruct HX as[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    first[assumption|apply Premises;cbn;tauto].
Qed.
Print Assumptions source_zfr_rec_omega_branch.

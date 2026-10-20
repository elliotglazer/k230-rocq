(** Uniform support bounds for the fixed five successor witness roles. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FixedSourceBounds CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone
 SourceNumeralLift SourceFiniteCutoffShift SourceDefinabilityPrimitives SourceEnvFDomainWitnessFixed SourceEnvFDomainWitnessTransport
 SourceEnvFDomainGraph SourceNumFUniqueSyntax SourceImplicationAllShift SourceQuantifierRules.
From OldZFC Require Z_base.
From PAModel Require Import OldNamedSyntaxBridge OldFullNDSourceBridge.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition ew_role_bound M n:=succM M(succM M(succM M(succM M(succM M n)))).
Theorem ew_raise_bound M f k:source_bounded M f k->source_bounded M f(succM M k).
Proof.
 intro H. apply(source_bounded_monotone M f k(succM M k)H).
 exact(coding_lt_trans M k(succM M k)(succM M(succM M k))(coding_lt_succ M k)(coding_lt_succ M(succM M k))).
Qed.
Theorem ew_fixed_bound M f r n:(r<=5)%nat->source_bounded M f(code_numeral M r)->source_bounded M f(ew_role_bound M n).
Proof.
 intros HR HF. apply(source_bounded_monotone M f(code_numeral M 5)(ew_role_bound M n)).
 - apply(source_bounded_monotone M f(code_numeral M r)(code_numeral M 5)HF).
   exact(proj2(fixed_source_numeral_lt_iff M r 6)ltac:(lia)).
 - unfold ew_role_bound. change(coding_lt M(succM M(succM M(succM M(succM M(succM M(zeroM M))))))(succM M(succM M(succM M(succM M(succM M(succM M n))))))).
   do 5 apply coding_lt_succ_cancel. apply coding_zero_lt_succ.
Qed.
Lemma ew_domain_shift_shape e d:(ew_domain e d)[↑]=ew_domain(S e)(S d).
Proof.
 unfold ew_domain. pose proof(isolated_old_formula_shift(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty e)(@OC.var OB.sig_empty d)))as E.
 rewrite OldZFC.Z_base.Dom0_subst in E. exact(eq_sym E).
Qed.
Theorem ew_domain_shift M e d:source_formula_shift M(ew_domain_code M e d)(ew_domain_code M(S e)(S d)).
Proof. pose proof(source_formula_numeral_shift M(ew_domain e d))as H. rewrite ew_domain_shift_shape in H. exact H. Qed.
Theorem ew_domain_fixed_bound M e d:(e<5)%nat->(d<5)%nat->source_bounded M(ew_domain_code M e d)(code_numeral M 5).
Proof.
 intros HE HD. exact(source_env_domain_bounded M(code_numeral M e)(code_numeral M d)(ew_domain_code M e d)(code_numeral M 5)
  (proj2(fixed_source_numeral_lt_iff M e 5)HE)(proj2(fixed_source_numeral_lt_iff M d 5)HD)(source_env_domain_old_numeral M e d)).
Qed.
Theorem ew_extension_bounds M:
 source_bounded M(code_numeral M(sf_encode ew_extension032))(code_numeral M 4)/\
 source_bounded M(code_numeral M(sf_encode ew_extension143))(code_numeral M 5).
Proof.
 assert(HCut:source_cutoff_shift M 1(code_numeral M(sf_encode source_def_extension021))(code_numeral M(sf_encode ew_extension032))).
 { exact(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M)source_def_extension021 _ _(source_formula_numeral_graph M source_def_extension021)(source_formula_numeral_graph M ew_extension032)). }
 pose proof(source_cutoff_shift_bounded M 1 _ _(code_numeral M 2)(numerical_def_extension_bound M)HCut)as B032.
 split;[exact B032|]. exact(source_shift_bound M _ _(code_numeral M 4)B032(source_formula_numeral_shift M ew_extension032)).
Qed.
Theorem ew_binary_bound M a b f k h:sf_binary h->sf_relation M h a b f->source_bounded M a k->source_bounded M b k->source_bounded M f k.
Proof. intros HH HF HA HB. exact(proj2(source_bounded_accept_binary M h a b f k HH HF)(conj HA HB)). Qed.
Theorem ew_exists_bound M a f k:sf_relation M SFEx a(zeroM M)f->source_bounded M a k->source_bounded M f k.
Proof. intros HE HA. exact(proj2(source_bounded_accept_unary M SFEx a f k(or_intror eq_refl)HE)(ew_raise_bound M a k HA)). Qed.
Print Assumptions ew_fixed_bound.
Print Assumptions ew_domain_shift.
Print Assumptions ew_extension_bounds.


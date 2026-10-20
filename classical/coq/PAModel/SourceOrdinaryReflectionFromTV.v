(** Close the literal ordinary Refl shell by actual BallS introduction,
    implication introduction and universal introduction. The mathematical
    witness and containment inputs remain explicit actual source proofs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceQuantifierRules
  SourceHierarchySyntax SourceSetRelativization SourceOrdinaryReflectionSyntax SourceTarskiVaughtInputs SourceTarskiVaughtBallS.
Unset Implicit Arguments.

Theorem source_full_ordinary_reflection_from_tv M domain phi count d refl level
    b c n sb sc ub uc un k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
  context_bounded M b c n k ->coding_lt M d k ->
  source_ordinary_reflection M domain count phi d refl ->
  source_LL_instance M(succM M d)(zeroM M)level ->context_shift M b c n sb sc ->
  environment_cons M sb sc n level ub uc un ->
  source_tv_witnesses M domain phi count(zeroM M)ub uc un ->
  source_tv_containment M domain(zeroM M)ub uc un ->source_full_prv M b c n refl.
Proof.
  intros HD HP BC HDk HRefl HLevel HShift HCons HW HC.
  pose proof(source_ordinary_reflection_bounded M domain count phi d refl k HD HP HDk HRefl)as BRefl.
  destruct HRefl as(left&right&equiv&block&level'&point&HL&HR&HE&HB&HLevel'&HPoint&HAll).
  pose proof(source_LL_instance_functional M(succM M d)(zeroM M)level level' HLevel HLevel')as E.
  subst level'.
  pose proof(context_shift_preserves_bound M b c n sb sc k HShift BC)as BShift.
  pose proof(source_LL_instance_bounded M(succM M d)(zeroM M)level(succM M k)
    (proj2(coding_lt_succ_cancel M d k)HDk)(coding_zero_lt_succ M k)HLevel)as BLevel.
  pose proof(proj2(context_bounded_cons M sb sc n level ub uc un(succM M k)HCons)(conj BLevel BShift))as BCons.
  assert(HR':source_set_relativization M(addM M count(zeroM M))phi right).
  { now rewrite coding_add_zero_r. }
  pose proof(source_full_tv_ballS M domain phi count(zeroM M)left right equiv block ub uc un(succM M k)
    HD HP BCons(coding_zero_lt_succ M k)HL HR' HE HB HW HC)as PBlock.
  pose proof(proj1(source_bounded_accept_unary M SFAll point refl k(or_introl eq_refl)HAll)BRefl)as BPoint.
  pose proof(full_source_II M sb sc n level block point ub uc un
    (ex_intro _ (succM M k)(conj BPoint BShift))PBlock HCons HPoint)as PPoint.
  exact(full_source_AllI M b c n point refl sb sc(ex_intro _ k(conj BRefl BC))PPoint HShift HAll).
Qed.

Print Assumptions source_full_ordinary_reflection_from_tv.

(** The literal upn/ext composition square for removing one bounded
    quantifier. Prefix lengths are arbitrary model values. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking
  CodeExpressions NumericalProofs NumericalSubstitutionMaps SourceInternalLifts SourceInternalLiftLaws SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Lemma balls_prefix_tail M b c n w:
  substitution_lookup M b c n(zeroM M)(addM M n w)w.
Proof.
  apply substitution_lookup_outside;[apply source_upn_not_lt_add|]. exists w. split;[reflexivity|].
  symmetry. apply coding_add_zero.
Qed.
Theorem balls_instantiation_composition M count b c t ib ic ub uc:
  beta M b c count t ->substitution_lookup M ib ic(code_numeral M 1)(zeroM M)(zeroM M)t ->
  source_upn_map M count ib ic(code_numeral M 1)(zeroM M)ub uc ->
  forall i j v,
    substitution_lookup M ub uc(addM M count(code_numeral M 1))(addM M count(zeroM M))i j ->
    substitution_lookup M b c count(zeroM M)j v ->
    substitution_lookup M b c(succM M count)(zeroM M)i v.
Proof.
  intros HT HHead HM i j v HFirst HSecond. apply(proj1(HM i j))in HFirst.
  destruct HFirst as[(HI&E)|(HI&q&w&HE&HW&EV)].
  - subst j. apply(proj1(substitution_lookup_inside M b c count(zeroM M)i v HI))in HSecond.
    apply substitution_lookup_inside;[apply coding_lt_succ_cases;now left|exact HSecond].
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)q)
      as[E|(s&E)];subst q.
    + pose proof(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)(zeroM M)w t HW HHead)as EW.
      subst w. rewrite coding_add_zero_r in HE. subst i j.
      pose proof(substitution_lookup_functional M b c count(zeroM M)(addM M count t)v t HSecond
        (balls_prefix_tail M b c count t))as E. subst v.
      apply substitution_lookup_inside;[apply coding_lt_succ|exact HT].
    + assert(EW:w=s).
      { exact(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)(succM M s)w s HW
          (substitution_singleton_tail M ib ic s)). }
      subst w j. pose proof(substitution_lookup_functional M b c count(zeroM M)(addM M count s)v s HSecond
        (balls_prefix_tail M b c count s))as E. subst v.
      change(i = addM M count(succM M s))in HE. rewrite internal_add_succ_right,<-Arithmetic.add_succ in HE.
      subst i. apply balls_prefix_tail.
Qed.
Print Assumptions balls_instantiation_composition.


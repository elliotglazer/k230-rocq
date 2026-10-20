(** Exact cancellation of the canonical cutoff-one insertions by actual
    binder instantiation. All matrices and variable bounds may be nonstandard. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenaming RenamingSubstitution
 SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceSubstitutionComposition SourceSubstitutionIdentity
 SourceShiftSpecialization SourceRepresentativeRenaming SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_cutoff_one_lifted_opening M f shifted bound ib ic lb lc ln:
 source_bounded M f bound ->source_cutoff_shift M 1 f shifted ->
 substitution_lift M ib ic(code_numeral M 1)(zeroM M)lb lc ln ->
 numerical_substitution M shifted lb lc ln(code_numeral M 1)f.
Proof.
 intros HB(sb&sc&sn&HMap&HShift)HLift.
 destruct(numerical_substitution_total M shifted lb lc ln(code_numeral M 1))as(out&HOut).
 assert(HRound:numerical_substitution M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)out).
 { apply(numerical_substitution_composition M f bound sb sc sn(code_numeral M 2)
    lb lc ln(code_numeral M 1)(zeroM M)(zeroM M)(zeroM M)(zeroM M)shifted out HB HShift HOut).
   intros i j v _ HJ HV.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[EI|[idx EI]];subst i.
   - assert(EJ:j=zeroM M)by(exact(substitution_lookup_functional M sb sc sn(code_numeral M 2)(zeroM M)j(zeroM M)
      HJ(source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HMap 0))). subst j.
     apply(proj1(substitution_lift_head M ib ic(code_numeral M 1)(zeroM M)lb lc ln v HLift))in HV.
     subst v. apply source_empty_substitution_lookup.
   - assert(EJ:j=succM M(succM M idx))by(exact(substitution_lookup_functional M sb sc sn(code_numeral M 2)(succM M idx)j _
      HJ(source_cutoff_shift_map_tail_lookup M 1 sb sc sn idx HMap))). subst j.
     pose proof(proj2(substitution_lift_tail M ib ic(code_numeral M 1)(zeroM M)lb lc ln(succM M idx)idx HLift)
      (substitution_singleton_tail M ib ic idx))as HExpected.
     assert(EV:v=succM M idx)by(exact(substitution_lookup_functional M lb lc ln(code_numeral M 1)
      (succM M(succM M idx))v(succM M idx)HV HExpected)). subst v.
     apply source_empty_substitution_lookup. }
 assert(HIdentity:numerical_substitution M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_substitution_identity_on_bound M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)bound HB).
   intros i _. apply source_empty_substitution_lookup. }
 pose proof(numerical_substitution_functional M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)out f HRound HIdentity)as E.
 now subst out.
Qed.

Theorem source_cutoff_one_open_representative M phi shifted x assigned bound:
 source_bounded M phi bound ->source_cutoff_shift M 1 phi shifted ->
 source_representative_renaming M x phi assigned ->numerical_instantiation M shifted x assigned.
Proof.
 intros HB(sb&sc&sn&HMap&HShift)HRep.
 destruct(numerical_instantiation_total M shifted x)as(out&ib&ic&HHead&HOpened).
 assert(RLookup:forall i j,representative_lookup M x i j ->
  substitution_lookup M x x(code_numeral M 1)(code_numeral M 1)i j).
 { intros i j HI. pose proof(proj1(renaming_substitution_lookup M x x(code_numeral M 1)(zeroM M)i j)HI)as H.
   now rewrite coding_add_zero_r in H. }
 assert(HRepSub:numerical_substitution M phi x x(code_numeral M 1)(code_numeral M 1)assigned).
 { apply(proj1(numerical_renaming_substitution M phi x x(code_numeral M 1)(zeroM M)assigned))in HRep.
   now rewrite coding_add_zero_r in HRep. }
 assert(HRound:numerical_substitution M phi x x(code_numeral M 1)(code_numeral M 1)out).
 { apply(numerical_substitution_composition M phi bound sb sc sn(code_numeral M 2)
    ib ic(code_numeral M 1)(zeroM M)x x(code_numeral M 1)(code_numeral M 1)shifted out HB HShift HOpened).
   intros i j v _ HJ HV.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[EI|[idx EI]];subst i.
   - assert(EJ:j=zeroM M)by(exact(substitution_lookup_functional M sb sc sn(code_numeral M 2)(zeroM M)j(zeroM M)
      HJ(source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HMap 0))). subst j.
     assert(EV:v=x)by(exact(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)(zeroM M)v x HV HHead)).
     subst v. apply RLookup,representative_lookup_zero.
   - assert(EJ:j=succM M(succM M idx))by(exact(substitution_lookup_functional M sb sc sn(code_numeral M 2)(succM M idx)j _
      HJ(source_cutoff_shift_map_tail_lookup M 1 sb sc sn idx HMap))). subst j.
     assert(EV:v=succM M idx)by(exact(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)
      (succM M(succM M idx))v(succM M idx)HV(substitution_singleton_tail M ib ic(succM M idx)))). subst v.
     apply RLookup,representative_lookup_nonzero. intro E. symmetry in E. exact(Model.zero_ne_succ M idx E). }
 pose proof(numerical_substitution_functional M phi x x(code_numeral M 1)(code_numeral M 1)out assigned HRound HRepSub)as E.
 subst out. exists ib,ic. auto.
Qed.
Print Assumptions source_cutoff_one_lifted_opening.
Print Assumptions source_cutoff_one_open_representative.

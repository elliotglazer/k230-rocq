(** Exact lookup-to-representation role action. Query0 is reopened at
    an arbitrary numerical name, environment1 becomes0, and assignment
    parameters move to3 and above. The matrix remains internally arbitrary. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 SourceFiniteNameParameters NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 RenamingSubstitution SourceQuantifierRules SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceBoundedMapComposition SourceSubstitutionComposition.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_atomic_lookup_map M name b c:=
 renaming_lookup M b c(code_numeral M 2)(code_numeral M 1)(zeroM M)name/\
 renaming_lookup M b c(code_numeral M 2)(code_numeral M 1)(code_numeral M 1)(zeroM M)/\
 forall i,renaming_lookup M b c(code_numeral M 2)(code_numeral M 1)(succM M(succM M i))(succM M(succM M(succM M i))).
Theorem source_atomic_lookup_map_total M name:exists b c,source_atomic_lookup_map M name b c.
Proof.
 set(rho:=fun i:nat=>match i with 0=>name|_=>zeroM M end).
 destruct(source_finite_names_total M 2 rho(code_numeral M 1))as(b&c&HN).
 exists b,c. split;[exact(HN 0 ltac:(lia))|]. split;[exact(HN 1 ltac:(lia))|].
 intro i. apply(proj2(renaming_lookup_outside M b c(code_numeral M 2)(code_numeral M 1)(succM M(succM M i))_
  ltac:(intro H;change(coding_lt M(succM M(succM M i))(succM M(succM M(zeroM M))))in H;
   exact(coding_not_lt_zero M i(proj1(coding_lt_succ_cancel M i(zeroM M))(proj1(coding_lt_succ_cancel M(succM M i)(succM M(zeroM M)))H)))))).
 change(succM M(succM M(succM M i))=addM M(succM M(succM M i))(code_numeral M 1)).
 rewrite(coding_add_comm M(succM M(succM M i))(code_numeral M 1)).
 change(succM M(succM M(succM M i))=addM M(succM M(zeroM M))(succM M(succM M i))).
 now rewrite Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Theorem source_atomic_lookup_environment_action M p first guard shifted name rb rc bound:
 source_bounded M p bound->source_cutoff_shift M 1 p first->source_cutoff_shift M 1 first guard->
 source_formula_shift M p shifted->source_atomic_lookup_map M name rb rc->
 numerical_renaming M shifted rb rc(code_numeral M 2)(code_numeral M 1)guard.
Proof.
 intros BP(ab&ac&an&HA&H1)(bb&bc&bn&HB&H2)HS(HZero&HOne&HTail).
 destruct(numerical_substitution_composition_total M p bound ab ac an(code_numeral M 2)
  bb bc bn(code_numeral M 2)first guard BP H1 H2)as(db&dc&HD&HDMap).
 destruct(numerical_renaming_total M shifted rb rc(code_numeral M 2)(code_numeral M 1))as(candidate&HCandidate).
 assert(HCompose:numerical_substitution M p db dc bound(zeroM M)candidate).
 { apply(numerical_substitution_composition M p bound(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
   rb rc(code_numeral M 2)(addM M(code_numeral M 2)(code_numeral M 1))db dc bound(zeroM M)shifted candidate BP
   (proj1(numerical_renaming_empty_substitution M p(zeroM M)(zeroM M)(code_numeral M 1)shifted)HS)
   (proj1(numerical_renaming_substitution M shifted rb rc(code_numeral M 2)(code_numeral M 1)candidate)HCandidate)).
   intros i j value HI HJ HV. apply(proj2(HDMap i value HI)).
   pose proof(substitution_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)i j _ HJ(source_cutoff_shift_base_lookup M i))as EJ. subst j.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|(idx&E)];subst i.
   - pose proof(substitution_lookup_functional M rb rc(code_numeral M 2)(addM M(code_numeral M 2)(code_numeral M 1))
     (code_numeral M 1)value(zeroM M)HV(proj1(renaming_substitution_lookup M rb rc(code_numeral M 2)(code_numeral M 1)_ _)HOne))as EV. subst value.
     exists(zeroM M). exact(conj(source_cutoff_shift_map_fixed_lookup M 1 ab ac an HA 0)(source_cutoff_shift_map_fixed_lookup M 1 bb bc bn HB 0)).
   - pose proof(substitution_lookup_functional M rb rc(code_numeral M 2)(addM M(code_numeral M 2)(code_numeral M 1))
     (succM M(succM M idx))value _ HV(proj1(renaming_substitution_lookup M rb rc(code_numeral M 2)(code_numeral M 1)_ _)(HTail idx)))as EV. subst value.
     exists(succM M(succM M idx)). exact(conj(source_cutoff_shift_map_tail_lookup M 1 ab ac an idx HA)
      (source_cutoff_shift_map_tail_lookup M 1 bb bc bn(succM M idx)HB)). }
 pose proof(numerical_substitution_functional M p db dc bound(zeroM M)candidate guard HCompose HD)as E. now subst candidate.
Qed.
Print Assumptions source_atomic_lookup_map_total.
Print Assumptions source_atomic_lookup_environment_action.

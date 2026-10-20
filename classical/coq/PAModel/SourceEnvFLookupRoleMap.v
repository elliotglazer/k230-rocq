(** A fixed two-entry role map for lookup: query0 becomes2, environment1
    stays1, and all assignment parameters move across three new roles. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 SourceFiniteNameParameters NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 RenamingSubstitution SourceQuantifierRules SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceBoundedMapComposition SourceFourMapComparison.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_env_lookup_role_map M b c:=
 renaming_lookup M b c(code_numeral M 2)(code_numeral M 3)(zeroM M)(code_numeral M 2)/\
 renaming_lookup M b c(code_numeral M 2)(code_numeral M 3)(code_numeral M 1)(code_numeral M 1)/\
 forall i,renaming_lookup M b c(code_numeral M 2)(code_numeral M 3)(succM M(succM M i))(succM M(succM M(succM M(succM M(succM M i))))).
Theorem source_env_lookup_role_map_total M:exists b c,source_env_lookup_role_map M b c.
Proof.
 set(rho:=fun i:nat=>match i with 0=>code_numeral M 2|_=>code_numeral M 1 end).
 destruct(source_finite_names_total M 2 rho(code_numeral M 3))as(b&c&HN).
 exists b,c. split;[exact(HN 0 ltac:(lia))|]. split;[exact(HN 1 ltac:(lia))|].
 intros i. apply(proj2(renaming_lookup_outside M b c(code_numeral M 2)(code_numeral M 3)
  (succM M(succM M i))_(ltac:(intro H;change(coding_lt M(succM M(succM M i))(succM M(succM M(zeroM M))))in H;exact(coding_not_lt_zero M i(proj1(coding_lt_succ_cancel M i(zeroM M))(proj1(coding_lt_succ_cancel M(succM M i)(succM M(zeroM M)))H))))))).
 change(succM M(succM M(succM M(succM M(succM M i))))=addM M(succM M(succM M i))(code_numeral M 3)).
 rewrite!Arithmetic.add_succ,(Arithmetic.add_comm M i(code_numeral M 3)).
 change(succM M(succM M(succM M(succM M(succM M i))))=succM M(succM M(addM M(succM M(succM M(succM M(zeroM M))))i))).
 now rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Theorem source_env_lookup_environment_action M p p1 p2 p3 ps out rb rc k:
 source_bounded M p k->source_cutoff_shift M 1 p p1->source_cutoff_shift M 1 p1 p2->source_cutoff_shift M 1 p2 p3->
 source_formula_shift M p ps->source_formula_shift M p3 out->source_env_lookup_role_map M rb rc->
 numerical_renaming M ps rb rc(code_numeral M 2)(code_numeral M 3)out.
Proof.
 intros BP(ab&ac&an&HA&H1)(bb&bc&bn&HB&H2)(cb&cc&cn&HC&H3)HPS HOut(HZero&HOne&HTail).
 destruct(numerical_renaming_total M ps rb rc(code_numeral M 2)(code_numeral M 3))as(candidate&HR).
 pose proof(proj1(numerical_renaming_empty_substitution M p(zeroM M)(zeroM M)(code_numeral M 1)ps)HPS)as HS.
 pose proof(proj1(numerical_renaming_substitution M ps rb rc(code_numeral M 2)(code_numeral M 3)candidate)HR)as HRC.
 destruct(numerical_substitution_composition_total M p k(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  rb rc(code_numeral M 2)(addM M(code_numeral M 2)(code_numeral M 3))ps candidate BP HS HRC)as(db&dc&HD&HDMap).
 assert(HCompose:numerical_substitution M p db dc k(zeroM M)out).
 { apply(numerical_four_substitutions_compare M p k ab ac an(code_numeral M 2)bb bc bn(code_numeral M 2)
    cb cc cn(code_numeral M 2)(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)db dc k(zeroM M)p1 p2 p3 out BP H1 H2 H3
    (proj1(numerical_renaming_empty_substitution M p3(zeroM M)(zeroM M)(code_numeral M 1)out)HOut)).
   intros i j1 j2 j3 value HI HH1 HH2 HH3 HH4. apply(proj2(HDMap i value HI)).
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
   - pose proof(substitution_lookup_functional M ab ac an(code_numeral M 2)(zeroM M)j1 _ HH1(source_cutoff_shift_map_fixed_lookup M 1 ab ac an HA 0))as E. subst j1.
     pose proof(substitution_lookup_functional M bb bc bn(code_numeral M 2)(zeroM M)j2 _ HH2(source_cutoff_shift_map_fixed_lookup M 1 bb bc bn HB 0))as E. subst j2.
     pose proof(substitution_lookup_functional M cb cc cn(code_numeral M 2)(zeroM M)j3 _ HH3(source_cutoff_shift_map_fixed_lookup M 1 cb cc cn HC 0))as E. subst j3.
     pose proof(substitution_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)(zeroM M)value _ HH4(source_cutoff_shift_base_lookup M(zeroM M)))as E. subst value.
     exists(code_numeral M 1). split;[apply source_cutoff_shift_base_lookup|].
     exact(proj1(renaming_substitution_lookup M rb rc(code_numeral M 2)(code_numeral M 3)_ _)HOne).
   - pose proof(substitution_lookup_functional M ab ac an(code_numeral M 2)(succM M idx)j1 _ HH1(source_cutoff_shift_map_tail_lookup M 1 ab ac an idx HA))as E. subst j1.
     pose proof(substitution_lookup_functional M bb bc bn(code_numeral M 2)(succM M(succM M idx))j2 _ HH2(source_cutoff_shift_map_tail_lookup M 1 bb bc bn(succM M idx)HB))as E. subst j2.
     pose proof(substitution_lookup_functional M cb cc cn(code_numeral M 2)(succM M(succM M(succM M idx)))j3 _ HH3(source_cutoff_shift_map_tail_lookup M 1 cb cc cn(succM M(succM M idx))HC))as E. subst j3.
     pose proof(substitution_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)(succM M(succM M(succM M(succM M idx))))value _ HH4(source_cutoff_shift_base_lookup M(succM M(succM M(succM M(succM M idx))))))as E. subst value.
     exists(succM M(succM M idx)). split;[apply source_cutoff_shift_base_lookup|].
     exact(proj1(renaming_substitution_lookup M rb rc(code_numeral M 2)(code_numeral M 3)_ _)(HTail idx)). }
 pose proof(numerical_substitution_functional M p db dc k(zeroM M)candidate out HD HCompose)as E. now subst candidate.
Qed.
Print Assumptions source_env_lookup_role_map_total.
Print Assumptions source_env_lookup_environment_action.



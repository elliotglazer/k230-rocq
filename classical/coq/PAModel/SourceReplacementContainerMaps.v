(** Removing the range container binder of Replacement leaves exactly the
    cutoff-two shift of its arbitrary internal matrix. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalContexts NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps
  NumericalSubstitution NumericalInstantiation RenamingSubstitution SubstitutionSource
  SourceBounded SourceSubstitutionIdentity SourceRenamingSquare SourceFiniteCutoffShift
  SourceCutoffShiftCommutation SourceShiftSpecialization SchemaRenamingDescriptors
  SourceReplacementProfileShift SourceSeparationContainerMaps.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_replacement_body_container_substitution M phi matrix p2 k A ub uc d e j v w l ab ac an :
  source_bounded M phi k ->schema_renaming M RepC phi matrix ->source_cutoff_shift M 2 phi p2 ->
  substitution_lookup M ub uc (code_numeral M 1) (zeroM M) (zeroM M) A ->
  substitution_lift M ub uc (code_numeral M 1) (zeroM M) d e j ->
  substitution_lift M d e j (code_numeral M 1) v w l ->
  substitution_lift M v w l (code_numeral M 2) ab ac an ->
  numerical_substitution M matrix ab ac an (code_numeral M 3) p2.
Proof.
  intros HB HMatrix (rb&rc&rn&HM&HS) HU HL1 HL2 HL3.
  pose proof(source_cutoff_shift_map_renaming M 2 phi p2 rb rc rn HM HS)as HR.
  assert(HI:numerical_substitution M phi (zeroM M)(zeroM M)(zeroM M)(zeroM M)phi).
  { apply(numerical_substitution_identity_on_bound M phi _ _ _ _ k HB).
    intros i _. apply source_empty_substitution_lookup. }
  apply(numerical_source_renaming_square M phi k
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 4)(code_numeral M 1)(code_numeral M 2)(code_numeral M 2)
    rb rc rn(code_numeral M 1)ab ac an(code_numeral M 3)
    phi matrix p2 HB HI HMatrix HR).
  intros i x y z HBound HX HZ HY.
  assert(EX:x=i)by(exact(substitution_lookup_functional M _ _ _ _ i x i HX(source_empty_substitution_lookup M i))).
  subst x. change(schema_lookup M RepC i y)in HY.
  apply(proj1(source_cutoff_shift_map_renaming_lookup M 2 rb rc rn i z HM))in HZ.
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
  - apply(proj1(schema_lookup_first M RepC y))in HY. change(y=zeroM M)in HY. subst y.
    pose proof(substitution_lookup_functional M rb rc rn(code_numeral M 3)_ z _ HZ
      (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HM 0))as EZ. subst z.
    exact(proj2(substitution_lift_head M v w l(code_numeral M 2)ab ac an(zeroM M)HL3)eq_refl).
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H)idx)as[E|[idx' E]];subst idx.
    + apply(proj1(schema_lookup_second M RepC y))in HY. change(y=code_numeral M 1)in HY. subst y.
      pose proof(substitution_lookup_functional M rb rc rn(code_numeral M 3)_ z _ HZ
        (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HM 1))as EZ. subst z.
      apply(proj2(substitution_lift_tail M v w l(code_numeral M 2)ab ac an(zeroM M)(zeroM M)HL3)).
      exact(proj2(substitution_lift_head M d e j(code_numeral M 1)v w l(zeroM M)HL2)eq_refl).
    + pose proof(renaming_lookup_functional M(code_numeral M 4)(code_numeral M 1)
        (code_numeral M 2)(code_numeral M 2)_ y _ HY(source_repc_tail_lookup M idx'))as EY. subst y.
      pose proof(substitution_lookup_functional M rb rc rn(code_numeral M 3)_ z _ HZ
        (source_cutoff_shift_map_tail_lookup M 2 rb rc rn idx' HM))as EZ. subst z.
      apply(proj2(substitution_lift_tail M v w l(code_numeral M 2)ab ac an
        (succM M(succM M(succM M idx')))(succM M(succM M idx'))HL3)).
      apply(proj2(substitution_lift_tail M d e j(code_numeral M 1)v w l
        (succM M(succM M idx'))(succM M idx')HL2)).
      apply(proj2(substitution_lift_tail M ub uc(code_numeral M 1)(zeroM M)d e j
        (succM M idx')idx' HL1)). apply substitution_singleton_tail.
Qed.

Lemma source_replacement_container_map_atoms M A ub uc d e j v w l ab ac an :
  substitution_lookup M ub uc(code_numeral M 1)(zeroM M)(zeroM M)A ->
  substitution_lift M ub uc(code_numeral M 1)(zeroM M)d e j ->
  substitution_lift M d e j(code_numeral M 1)v w l ->
  substitution_lift M v w l(code_numeral M 2)ab ac an ->
  substitution_lookup M ab ac an(code_numeral M 3)(zeroM M)(zeroM M) /\
  substitution_lookup M ab ac an(code_numeral M 3)(code_numeral M 3)(source_succ_iter M 3 A).
Proof.
  intros HU HL1 HL2 HL3. split.
  - exact(proj2(substitution_lift_head M v w l(code_numeral M 2)ab ac an(zeroM M)HL3)eq_refl).
  - apply(proj2(substitution_lift_tail M v w l(code_numeral M 2)ab ac an
      (code_numeral M 2)(source_succ_iter M 2 A)HL3)).
    exact(proj2(proj2(source_separation_container_map_atoms M A ub uc d e j v w l HU HL1 HL2))).
Qed.
Print Assumptions source_replacement_body_container_substitution.
Print Assumptions source_replacement_container_map_atoms.

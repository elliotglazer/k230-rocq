(** Opening a raw binder at a name above every old free parameter and then
    closing that name recovers the original body. Bounds and names are internal. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming SubstitutionSource
 SourceSubstitutionRenaming SourceSubstitutionIdentity SourceShiftSpecialization RawBinderRenaming SourceNamedQuantifierRules.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_fresh_named_opening_closes M body opened x k rb rc closed:
 source_bounded M body(succM M k) ->coding_lt M k(succM M x) ->
 numerical_instantiation M body x opened ->raw_binder_renaming M x rb rc ->
 numerical_renaming M opened rb rc(succM M x)(code_numeral M 1)closed ->closed=body.
Proof.
 intros HB HFresh(ib&ic&HHead&HOpened)HRaw HClosed.
 assert(Fresh:forall i,coding_lt M i k ->i<>x).
 { intros i HI. exact(@Peano.lt_neq(carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)i x(source_bound_lt_le M i k x HI HFresh)). }
 assert(HIdentity:numerical_substitution M body(zeroM M)(zeroM M)(zeroM M)(zeroM M)body).
 { apply(numerical_substitution_identity_on_bound M body(zeroM M)(zeroM M)(zeroM M)(zeroM M)(succM M k)HB).
   intros i _. exact(source_empty_substitution_lookup M i). }
 assert(HRound:numerical_substitution M body(zeroM M)(zeroM M)(zeroM M)(zeroM M)closed).
 { apply(numerical_substitution_then_renaming M body(succM M k)
    ib ic(code_numeral M 1)(zeroM M)rb rc(succM M x)(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)opened closed HB HOpened HClosed).
   intros i j v HI HLookup HMap.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[EI|[i' EI]];subst i.
   - assert(EJ:j=x)by(exact(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)(zeroM M)j x HLookup HHead)).
     subst j. apply(proj1(HRaw x v))in HMap.
     destruct HMap as[[_ EV]|[HNeq _]];[subst v;apply source_empty_substitution_lookup|contradiction].
   - assert(EJ:j=i')by(exact(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)(succM M i')j i'
      HLookup(substitution_singleton_tail M ib ic i'))).
     subst j. apply(proj1(HRaw i' v))in HMap.
     destruct HMap as[[EI _]|[_ EV]].
     + exfalso. exact(Fresh i'(proj1(coding_lt_succ_cancel M i' k)HI)EI).
     + subst v. apply source_empty_substitution_lookup. }
 exact(numerical_substitution_functional M body(zeroM M)(zeroM M)(zeroM M)(zeroM M)closed body HRound HIdentity).
Qed.

Theorem source_fresh_instantiation_named_quantifier M(universal:bool)body out x opened k:
 source_bounded M body(succM M k) ->coding_lt M k(succM M x) ->
 numerical_instantiation M body x opened ->
 sf_relation M(if universal then SFAll else SFEx)body(zeroM M)out ->
 source_named_quantifier M universal x opened out.
Proof.
 intros HB HF HI HQ.
 destruct(raw_binder_renaming_total M x)as(rb&rc&HRaw).
 destruct(numerical_renaming_total M opened rb rc(succM M x)(code_numeral M 1))as(closed&HClosed).
 pose proof(source_fresh_named_opening_closes M body opened x k rb rc closed HB HF HI HRaw HClosed)as E.
 subst closed. exists rb,rc,body. auto.
Qed.
Print Assumptions source_fresh_named_opening_closes.
Print Assumptions source_fresh_instantiation_named_quantifier.

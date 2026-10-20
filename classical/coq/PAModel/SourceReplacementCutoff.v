(** Two insertions above the two Replacement variables are exactly the
    actual RepC renaming: fix 0 and 1, move every remaining index by two. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 SchemaRenamingDescriptors NumericalRenamingMaps RenamingSubstitution NumericalSubstitutionMaps NumericalSubstitution
 SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceSubstitutionComposition.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_cutoff_two_twice_replacement M f a b k:
 source_bounded M f k ->source_cutoff_shift M 2 f a ->source_cutoff_shift M 2 a b ->
 schema_renaming M RepC f b.
Proof.
 intros BF(ab&ac&an&HA&HF)(rb&rc&rn&HR&HG).
 unfold schema_renaming. cbn[schema_dividend schema_modulus schema_length schema_delta].
 apply(proj2(numerical_renaming_substitution M f(code_numeral M 4)(code_numeral M 1)
  (code_numeral M 2)(code_numeral M 2)b)).
 rewrite descriptor_numeral_add.
 apply(numerical_substitution_composition M f k ab ac an(code_numeral M 3)
  rb rc rn(code_numeral M 3)(code_numeral M 4)(code_numeral M 1)(code_numeral M 2)(code_numeral M 4)a b BF HF HG).
 intros i j v HI HJ HV.
 assert(Target:forall index value,schema_lookup M RepC index value ->
  substitution_lookup M(code_numeral M 4)(code_numeral M 1)(code_numeral M 2)(code_numeral M 4)index value).
 { intros index value HH. unfold schema_lookup in HH. cbn[schema_dividend schema_modulus schema_length schema_delta]in HH.
   pose proof(proj1(renaming_substitution_lookup M(code_numeral M 4)(code_numeral M 1)
    (code_numeral M 2)(code_numeral M 2)index value)HH)as H.
   now rewrite descriptor_numeral_add in H. }
 apply Target.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
 - pose proof(substitution_lookup_functional M ab ac an(code_numeral M 3)(zeroM M)j(zeroM M)HJ
    (source_cutoff_shift_map_fixed_lookup M 2 ab ac an HA 0))as E;subst j.
   pose proof(substitution_lookup_functional M rb rc rn(code_numeral M 3)(zeroM M)v(zeroM M)HV
    (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HR 0))as E;subst v.
   apply(proj2(schema_lookup_first M RepC(zeroM M))). reflexivity.
 - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)idx)as[E|[tail E]];subst idx.
   + pose proof(substitution_lookup_functional M ab ac an(code_numeral M 3)(code_numeral M 1)j(code_numeral M 1)HJ
      (source_cutoff_shift_map_fixed_lookup M 2 ab ac an HA 1))as E;subst j.
     pose proof(substitution_lookup_functional M rb rc rn(code_numeral M 3)(code_numeral M 1)v(code_numeral M 1)HV
      (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HR 1))as E;subst v.
     apply(proj2(schema_lookup_second M RepC(code_numeral M 1))). reflexivity.
   + pose proof(substitution_lookup_functional M ab ac an(code_numeral M 3)(succM M(succM M tail))j
      (succM M(succM M(succM M tail)))HJ(source_cutoff_shift_map_tail_lookup M 2 ab ac an tail HA))as E;subst j.
     pose proof(substitution_lookup_functional M rb rc rn(code_numeral M 3)(succM M(succM M(succM M tail)))v
      (succM M(succM M(succM M(succM M tail))))HV(source_cutoff_shift_map_tail_lookup M 2 rb rc rn(succM M tail)HR))as E;subst v.
     apply(proj2(schema_lookup_tail M RepC(succM M(succM M tail))(succM M(succM M(succM M(succM M tail))))
      ltac:(intro H;apply(proj1(coding_lt_succ_cancel M(succM M tail)(succM M(zeroM M))))in H;
       apply(proj1(coding_lt_succ_cancel M tail(zeroM M)))in H;exact(coding_not_lt_zero M tail H)))).
     change(succM M(succM M(succM M(succM M tail)))=addM M(succM M(succM M tail))(code_numeral M 2)).
     rewrite(Arithmetic.add_comm M(succM M(succM M tail))(code_numeral M 2)).
     change(succM M(succM M(succM M(succM M tail)))=addM M(succM M(succM M(zeroM M)))(succM M(succM M tail))).
     now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Print Assumptions source_cutoff_two_twice_replacement.

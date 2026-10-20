(** Exact literal RR correspondence with the actual RepA/RepB/RepC maps. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded SourceNumeralLift FixedSourceBounds
 NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
 SchemaRenamingDescriptors SourceRecursionRangeRelation.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_rec_rr_from_renaming M phi z v o a N old z' v' o' a' N' new rb rc rn delta:
 source_bounded M phi(code_numeral M 2) ->source_rec_rr M phi z v o a N old ->numerical_renaming M old rb rc rn delta new ->
 renaming_lookup M rb rc rn delta z z' ->renaming_lookup M rb rc rn delta v v' ->renaming_lookup M rb rc rn delta o o' ->
 renaming_lookup M rb rc rn delta a a' ->renaming_lookup M rb rc rn delta N N' ->source_rec_rr M phi z' v' o' a' N' new.
Proof.
 intros BP HO HR HZ HV HOO HAA HNN.
 destruct(source_rec_rr_total M phi z' v' o' a' N')as(other&HOther).
 pose proof(source_rec_rr_substitution M phi z v o a N old z' v' o' a' N' other rb rc rn(addM M rn delta)BP HO HOther
  (proj1(renaming_substitution_lookup M rb rc rn delta z z')HZ)(proj1(renaming_substitution_lookup M rb rc rn delta v v')HV)
  (proj1(renaming_substitution_lookup M rb rc rn delta o o')HOO)(proj1(renaming_substitution_lookup M rb rc rn delta a a')HAA)
  (proj1(renaming_substitution_lookup M rb rc rn delta N N')HNN))as HS.
 pose proof(numerical_substitution_functional M old rb rc rn(addM M rn delta)other new HS(proj1(numerical_renaming_substitution M old rb rc rn delta new)HR))as E.
 now subst other.
Qed.
Lemma source_schema_lookup_later M s i:(2<=i)%nat ->schema_lookup M s(code_numeral M i)(code_numeral M(i+schema_delta s)).
Proof.
 intro HI. apply schema_lookup_tail.
 - intro HBad. apply(proj1(fixed_source_numeral_lt_iff M i(schema_length s)))in HBad. destruct s;cbn[schema_length]in HBad;lia.
 - symmetry. apply descriptor_numeral_add.
Qed.
Theorem source_rec_rr_schema M phi matrix s out:
 source_bounded M phi(code_numeral M 2) ->source_rec_rr M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(code_numeral M 4)matrix ->
 schema_renaming M s matrix out ->source_rec_rr M phi(code_numeral M(schema_first s))(code_numeral M(schema_second s))
 (code_numeral M(2+schema_delta s))(code_numeral M(3+schema_delta s))(code_numeral M(4+schema_delta s))out.
Proof.
 intros BP HM HR. apply(source_rec_rr_from_renaming M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(code_numeral M 4)matrix
  (code_numeral M(schema_first s))(code_numeral M(schema_second s))(code_numeral M(2+schema_delta s))(code_numeral M(3+schema_delta s))(code_numeral M(4+schema_delta s))out
  (code_numeral M(schema_dividend s))(code_numeral M(schema_modulus s))(code_numeral M(schema_length s))(code_numeral M(schema_delta s))BP HM HR).
 - apply schema_lookup_first. reflexivity.
 - apply schema_lookup_second. reflexivity.
 - exact(source_schema_lookup_later M s 2 ltac:(lia)).
 - exact(source_schema_lookup_later M s 3 ltac:(lia)).
 - exact(source_schema_lookup_later M s 4 ltac:(lia)).
Qed.
Print Assumptions source_rec_rr_from_renaming.
Print Assumptions source_schema_lookup_later.
Print Assumptions source_rec_rr_schema.

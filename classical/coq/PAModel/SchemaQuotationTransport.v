(** Safe quotation transport for the four actual Separation/Replacement
    body renamings. The source formula and its bound may be nonstandard.
    This is syntax transport only, not a proof of a schema's K image. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SourceBounded NumericalEnvironments NumericalQuotation
  QuotationHygiene SchemaRenamingDescriptors RenamingSubstitution
  SubstitutionEnvironment SubstitutionEnvironmentTotal.
Unset Implicit Arguments.

Definition schema_substitution_base M kind :=
  addM M (code_numeral M (schema_length kind))
    (code_numeral M (schema_delta kind)).

Lemma schema_substitution_base_value M kind :
  schema_substitution_base M kind = code_numeral M
    (match kind with RepC => 4 | _ => 3 end).
Proof.
  unfold schema_substitution_base. rewrite descriptor_numeral_add.
  destruct kind; reflexivity.
Qed.

Theorem schema_quotation_safe_transport_exists M kind phi body bound
    eb ec en fresh domain :
  source_bounded M phi bound -> schema_renaming M kind phi body ->
  quotation_safe M eb ec en fresh domain ->
  exists fb fc,
    substitution_environment_agreement M
      (code_numeral M (schema_dividend kind))
      (code_numeral M (schema_modulus kind))
      (code_numeral M (schema_length kind))
      (schema_substitution_base M kind) eb ec en fb fc bound bound /\
    quotation_safe M fb fc bound fresh domain /\
    forall quoted,
      numerical_quotation M phi fb fc bound fresh domain quoted <->
      numerical_quotation M body eb ec en fresh domain quoted.
Proof.
  intros HBound HRenamed HSafe.
  apply (quotation_substitution_safe_transport_exists M phi body bound
    (code_numeral M (schema_dividend kind))
    (code_numeral M (schema_modulus kind))
    (code_numeral M (schema_length kind))
    (schema_substitution_base M kind) eb ec en fresh domain HBound).
  - apply (proj1 (numerical_renaming_substitution M phi
      (code_numeral M (schema_dividend kind))
      (code_numeral M (schema_modulus kind))
      (code_numeral M (schema_length kind))
      (code_numeral M (schema_delta kind)) body)). exact HRenamed.
  - exact HSafe.
Qed.

Print Assumptions schema_substitution_base_value.
Print Assumptions schema_quotation_safe_transport_exists.

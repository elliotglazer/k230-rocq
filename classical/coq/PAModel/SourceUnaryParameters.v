(** A one-free-variable fixed predicate can use any parameter-expression
    environment. Its unused entries are eliminated using the proved bound. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceFiniteParameters SourceFiniteParameterSubstitution SourceFiniteParameterBounds
  NumericalSubstitutionMaps NumericalInstantiation.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_unary_parameter_instantiation M phi names rho name out :
  bounded 1 phi ->code_relation M rho (names 0) name ->
  code_relation M rho (source_parameter_expression names phi) out ->
  numerical_instantiation M (code_numeral M (sf_encode phi)) name out.
Proof.
  intros HB HName HO.
  set (normalized:=fun i:nat=>match i with 0=>names 0 | S j=>CEconst j end).
  assert (HGraph:code_relation M rho (source_parameter_expression normalized phi) out).
  { rewrite <- (source_parameter_bounded_extensional 1 phi HB names normalized);[exact HO|].
    intros [|i] HI;[reflexivity|lia]. }
  destruct (substitution_singleton_total M name) as (b&c&HHead&HTail).
  exists b,c. split;[exact HHead|].
  apply (source_finite_parameter_substitution M phi normalized rho b c
    (succM M (zeroM M)) (zeroM M) out);[|exact HGraph].
  intros [|i] x HX;cbn [normalized] in HX.
  - pose proof (code_relation_functional M (names 0) rho x name HX HName) as E. now subst x.
  - change (x=code_numeral M i) in HX. subst x. exact (HTail (code_numeral M i)).
Qed.

Print Assumptions source_unary_parameter_instantiation.

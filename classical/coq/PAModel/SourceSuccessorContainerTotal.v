(** Generate the actual ordinal-successor container proof at an arbitrary name. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation
  SourceOrdinalPredicate SourceLeastOrdinalFixed SourceSuccessorContainerShell SourceZFRProvability.
Unset Implicit Arguments.

Theorem source_zfr_successor_container_total M g :exists ordinal container body member law,
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal /\
  sf_relation M SFImpl ordinal container law /\sf_relation M SFEx body(zeroM M)container /\
  sf_relation M SFAnd(source_ordinal_predicate_code M)member body /\
  sf_relation M SFMember(succM M g)(zeroM M)member /\source_zfr_provable M law.
Proof.
  set(rho:=fun _:nat=>g).
  destruct(code_relation_total M(least_fixed_parameter_expression LeastSuccessorContainer)rho) as(law&HL).
  destruct(source_successor_container_shell M rho law HL) as(ordinal&container&body&member&HO&HI&HE&HB&HM).
  exists ordinal,container,body,member,law. split;[exact HO|]. split;[exact HI|]. split;[exact HE|].
  split;[exact HB|]. split;[exact HM|]. exact(source_zfr_least_fixed_parameters M LeastSuccessorContainer rho law HL).
Qed.

Print Assumptions source_zfr_successor_container_total.

From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceNumeralLift SourceSubstitutionIdentity
 SourceRoleReopening SourcePieceClosure SourcePieceClosureFacts SourceRecursionBinaryInstance.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_rec_binary_identity M phi:source_bounded M phi(code_numeral M 2) ->source_rec_binary M phi(zeroM M)(code_numeral M 1)phi.
Proof.
 intro BP. destruct(source_role_reopening_total M(code_numeral M 1)(zeroM M))as(b&c&HR).
 exists b,c. split;[exact HR|]. apply(numerical_substitution_identity_on_bound M phi b c(code_numeral M 2)(code_numeral M 2)(code_numeral M 2)BP).
 intros i HI. destruct(source_numeral_initial_segment M 2 i HI)as(n&HN&->).
 pose proof(source_pc_reopening_lookup M(code_numeral M 1)(zeroM M)b c(code_numeral M 2)n HR HN)as HL.
 destruct n as[|[|n]];try lia;exact HL.
Qed.
Print Assumptions source_rec_binary_identity.

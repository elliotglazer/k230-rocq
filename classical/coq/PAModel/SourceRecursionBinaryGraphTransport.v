(** Exact transport to a chosen binary instance, not just a total output. *)
From PAModel Require Import Model FiniteCoding SourceBounded NumericalSubstitutionMaps NumericalSubstitution
 SourceRecursionBinaryInstance SourceRecursionBinaryTransport.
Unset Implicit Arguments.
Theorem source_rec_binary_substitution_graph M phi u v out u' v' out' rb rc rn base:
 source_bounded M phi(CodeExpressions.code_numeral M 2) ->source_rec_binary M phi u v out ->source_rec_binary M phi u' v' out' ->
 substitution_lookup M rb rc rn base u u' ->substitution_lookup M rb rc rn base v v' ->
 numerical_substitution M out rb rc rn base out'.
Proof.
 intros BP HO HN HU HV.
 destruct(numerical_substitution_total M out rb rc rn base)as(tmp&HT).
 pose proof(source_rec_binary_substitution M phi u v out rb rc rn base tmp u' v' BP HO HT HU HV)as HG.
 rewrite(source_rec_binary_functional M phi u' v' tmp out' HG HN)in HT. exact HT.
Qed.
Print Assumptions source_rec_binary_substitution_graph.

(** Exact cutoff2 insertion in the RR matrix, preserving both relation roles. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceRecursionRangeRelation.
Unset Implicit Arguments.
Theorem source_rec_rr_cutoff_two M phi o a N old new:
 source_bounded M phi(code_numeral M 2) ->
 source_rec_rr M phi(zeroM M)(code_numeral M 1)(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))old ->
 source_rec_rr M phi(zeroM M)(code_numeral M 1)(succM M(succM M(succM M o)))(succM M(succM M(succM M a)))(succM M(succM M(succM M N)))new ->
 source_cutoff_shift M 2 old new.
Proof.
 intros BP HO HN. destruct(source_cutoff_shift_map_total M 2)as(b&c&n&HM). exists b,c,n. split;[exact HM|].
 exact(source_rec_rr_substitution M phi(zeroM M)(code_numeral M 1)(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))old
  (zeroM M)(code_numeral M 1)(succM M(succM M(succM M o)))(succM M(succM M(succM M a)))(succM M(succM M(succM M N)))new b c n(code_numeral M 3)BP HO HN
  (source_cutoff_shift_map_fixed_lookup M 2 b c n HM 0)(source_cutoff_shift_map_fixed_lookup M 2 b c n HM 1)
  (source_cutoff_shift_map_tail_lookup M 2 b c n o HM)(source_cutoff_shift_map_tail_lookup M 2 b c n a HM)(source_cutoff_shift_map_tail_lookup M 2 b c n N HM)).
Qed.
Print Assumptions source_rec_rr_cutoff_two.

(** Exact cutoff insertion and functionality for the internal ExA recipe. *)
From PAModel Require Import Model FiniteCoding SetFormulaCodes SourceBounded CodeExpressions
 SourceRecursionAttempt SourceRecursionAppExists SourceRecursionPrimitiveRelations SourceRecursionExistsAttempt
 SourceFiniteCutoffShift SourceCutoffShiftCommutation.
Unset Implicit Arguments.
Theorem source_rec_app_exists_functional M f z x y:
 source_rec_app_exists M f z x ->source_rec_app_exists M f z y ->x=y.
Proof.
 intros(app&HA&HX)(app'&HA'&HY).
 pose proof(code_relation_functional M _ _ app' app HA' HA)as E. subst app'.
 exact(sf_relation_functional M SFEx app(zeroM M)x y HX HY).
Qed.
Theorem source_rec_exa_functional M phi z o a N x y:
 source_rec_exa M phi z o a N x ->source_rec_exa M phi z o a N y ->x=y.
Proof.
 intros(att&some&body&HT&HS&HB&HX)(att'&some'&body'&HT'&HS'&HB'&HY).
 pose proof(source_rec_attempt_functional M phi(succM M o)(succM M a)(succM M N)(zeroM M)att' att HT' HT)as E. subst att'.
 pose proof(source_rec_app_exists_functional M(zeroM M)(succM M z)some' some HS' HS)as E. subst some'.
 pose proof(sf_relation_functional M SFAnd att some body' body HB' HB)as E. subst body'.
 exact(sf_relation_functional M SFEx body(zeroM M)x y HX HY).
Qed.
Theorem source_rec_exa_cutoff_one M phi o a N old new:
 source_bounded M phi(code_numeral M 2) ->
 source_rec_exa M phi(zeroM M)(succM M o)(succM M a)(succM M N)old ->
 source_rec_exa M phi(zeroM M)(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))new ->
 source_cutoff_shift M 1 old new.
Proof.
 intros BP HO HN. destruct(source_cutoff_shift_map_total M 1)as(b&c&n&HM).
 exists b,c,n. split;[exact HM|].
 exact(source_rec_exa_substitution M phi(zeroM M)(succM M o)(succM M a)(succM M N)old
  (zeroM M)(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))new b c n(code_numeral M 2)BP HO HN
  (source_cutoff_shift_map_fixed_lookup M 1 b c n HM 0)
  (source_cutoff_shift_map_tail_lookup M 1 b c n o HM)
  (source_cutoff_shift_map_tail_lookup M 1 b c n a HM)
  (source_cutoff_shift_map_tail_lookup M 1 b c n N HM)).
Qed.
Print Assumptions source_rec_app_exists_functional.
Print Assumptions source_rec_exa_functional.
Print Assumptions source_rec_exa_cutoff_one.

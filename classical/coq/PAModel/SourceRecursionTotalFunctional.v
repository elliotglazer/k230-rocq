(** Functionality of the literal total-relation code graphs. *)
From PAModel Require Import Model SetFormulaCodes SourceRecursionBinaryInstance SourceRecursionTotalRelation.
Unset Implicit Arguments.
Theorem source_rec_relation_witness_functional M phi v x y:
 source_rec_relation_witness M phi v x ->source_rec_relation_witness M phi v y ->x=y.
Proof.
 intros(body&HB&HX)(body'&HB'&HY).
 pose proof(source_rec_binary_functional M phi(succM M v)(zeroM M)body' body HB' HB)as E. subst body'.
 exact(sf_relation_functional M SFEx body(zeroM M)x y HX HY).
Qed.
Theorem source_rec_total_relation_functional M phi x y:
 source_rec_total_relation M phi x ->source_rec_total_relation M phi y ->x=y.
Proof.
 intros(witness&HW&HX)(witness'&HW'&HY).
 pose proof(source_rec_relation_witness_functional M phi(zeroM M)witness' witness HW' HW)as E. subst witness'.
 exact(sf_relation_functional M SFAll witness(zeroM M)x y HX HY).
Qed.
Print Assumptions source_rec_relation_witness_functional.
Print Assumptions source_rec_total_relation_functional.

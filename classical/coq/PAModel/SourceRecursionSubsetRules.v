(** The actual two directions of the agreement-subset characterization. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes NumericalContexts NumericalSourceFull SourceTraceBounds
 SourceRecursionPrimitiveRelations SourceRecursionAgreementSubset SourcePieceBoundMaxJoint SourceDerivedRules SourceInstantiationConstructors.
Unset Implicit Arguments.
Theorem source_full_rec_subset_point_out M cb cc cn f g N X z point mx mn agr:
 source_rec_subset_point M f g N X z point ->sf_relation M SFMember z X mx ->sf_relation M SFMember z N mn ->source_rec_agreement M f g z agr ->
 source_full_prv M cb cc cn point ->source_full_prv M cb cc cn mx ->
 source_full_prv M cb cc cn mn /\source_full_prv M cb cc cn agr.
Proof.
 intros HP HX HN HA PP PX.
 destruct(source_rec_subset_point_shell M f g N X z point HP)as(mx'&mn'&agr'&both&forward&backward&HX'&HN'&HA'&HB&HF&HR&HO).
 pose proof(sf_relation_functional M SFMember z X mx' mx HX' HX)as E. subst mx'.
 pose proof(sf_relation_functional M SFMember z N mn' mn HN' HN)as E. subst mn'.
 pose proof(code_relation_functional M _ _ agr' agr HA' HA)as E. subst agr'.
 destruct(source_full_piece_conjunction_components M cb cc cn forward backward point HO PP)as[PF PR].
 pose proof(source_full_modus_ponens M cb cc cn mx both forward HF PF PX)as PB.
 exact(source_full_piece_conjunction_components M cb cc cn mn agr both HB PB).
Qed.
Theorem source_full_rec_subset_point_in M cb cc cn f g N X z point mx mn agr:
 source_rec_subset_point M f g N X z point ->sf_relation M SFMember z X mx ->sf_relation M SFMember z N mn ->source_rec_agreement M f g z agr ->
 source_full_prv M cb cc cn point ->source_full_prv M cb cc cn mn ->source_full_prv M cb cc cn agr ->source_full_prv M cb cc cn mx.
Proof.
 intros HP HX HN HA PP PN PA.
 destruct(source_rec_subset_point_shell M f g N X z point HP)as(mx'&mn'&agr'&both&forward&backward&HX'&HN'&HA'&HB&HF&HR&HO).
 pose proof(sf_relation_functional M SFMember z X mx' mx HX' HX)as E. subst mx'.
 pose proof(sf_relation_functional M SFMember z N mn' mn HN' HN)as E. subst mn'.
 pose proof(code_relation_functional M _ _ agr' agr HA' HA)as E. subst agr'.
 destruct(source_full_piece_conjunction_components M cb cc cn forward backward point HO PP)as[PF PR].
 assert(PB:source_full_prv M cb cc cn both).
 { exact(full_source_CI M cb cc cn mn agr both(source_wf_binary M cb cc cn SFAnd mn agr both(or_introl eq_refl)HB
   (source_full_prv_wellformed M cb cc cn mn PN)(source_full_prv_wellformed M cb cc cn agr PA))PN PA HB). }
 exact(source_full_modus_ponens M cb cc cn both mx backward HR PR PB).
Qed.
Theorem source_full_rec_subset_chart_out M cb cc cn f g N X z chart mx mn agr:
 source_rec_subset_chart M f g N X chart ->sf_relation M SFMember z X mx ->sf_relation M SFMember z N mn ->source_rec_agreement M f g z agr ->
 source_full_prv M cb cc cn chart ->source_full_prv M cb cc cn mx ->source_full_prv M cb cc cn mn /\source_full_prv M cb cc cn agr.
Proof.
 intros HC HX HN HA PC PX. destruct(source_rec_subset_point_total M f g N X z)as(point&HP).
 exact(source_full_rec_subset_point_out M cb cc cn f g N X z point mx mn agr HP HX HN HA
  (source_full_rec_subset_chart_use M cb cc cn f g N X chart z point HC HP PC)PX).
Qed.
Theorem source_full_rec_subset_chart_in M cb cc cn f g N X z chart mx mn agr:
 source_rec_subset_chart M f g N X chart ->sf_relation M SFMember z X mx ->sf_relation M SFMember z N mn ->source_rec_agreement M f g z agr ->
 source_full_prv M cb cc cn chart ->source_full_prv M cb cc cn mn ->source_full_prv M cb cc cn agr ->source_full_prv M cb cc cn mx.
Proof.
 intros HC HX HN HA PC PN PA. destruct(source_rec_subset_point_total M f g N X z)as(point&HP).
 exact(source_full_rec_subset_point_in M cb cc cn f g N X z point mx mn agr HP HX HN HA
  (source_full_rec_subset_chart_use M cb cc cn f g N X chart z point HC HP PC)PN PA).
Qed.
Print Assumptions source_full_rec_subset_point_out.
Print Assumptions source_full_rec_subset_point_in.
Print Assumptions source_full_rec_subset_chart_out.
Print Assumptions source_full_rec_subset_chart_in.

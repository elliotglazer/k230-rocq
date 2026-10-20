(** Genuine PA-definable induction on the internally finite parameter
    count. All source proof production is literal and covers nonstandard n. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalSourceFull
 SourceFiniteTelescope SourceConjunctionRules SourceCofinalGeometry SourceCofinalCommonRecipe SourceCofinalCommonZero
 SourceCofinalCommonSuccessorZFR SourceCofinalRequest SourceCofinalFiniteRules SourceCofinalFrameBounds SourceMembershipBlocks SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_cofinal_common_uniform M:forall count,source_cofinal_proof_at M count.
Proof.
 apply(definable_induction M(source_cofinal_proof_at M)(source_cofinal_proof_definable M)).
 - intros start Ks Lb seed member ordinals cover block target result HM HO HC HB HT HResult.
   pose proof(proj1(source_cofinal_request_telescope M member ordinals cover block target result)HResult)as HRT.
   destruct(sf_relation_total M SFImpl ordinals target)as(tail&HTail).
   destruct(sf_relation_total M SFImpl member tail)as(base&HBase).
   pose proof(source_zfr_cofinal_common_zero M Ks seed start member ordinals target tail base HM HO HT HTail HBase)as PBase.
   assert(HBaseTel:source_finite_telescope M[member;ordinals]target base).
   { exists tail. split;[exists target;split;[reflexivity|exact HTail]|exact HBase]. }
   destruct(source_cofinal_frame_bounds M start(zeroM M)Ks Lb seed member ordinals cover block target HM HO HC HB HT)as(k&BA&BT).
   apply(source_zfr_finite_telescope_rule M[base][member;ordinals;cover;block]target result k).
   + intros f[<-|[]]. exact PBase.
   + exact BA.
   + exact BT.
   + exact HRT.
   + intros b c n HCtx PK PA.
     apply(source_full_finite_telescope_apply M[member;ordinals]target base HBaseTel b c n(PK base ltac:(cbn;tauto))).
     intros f[<-|[<-|[]]];apply PA;cbn;tauto.
 - intros count IH start Ks Lb seed member ordinals cover block target result HM HO HC HB HT HResult.
   pose proof HB as HBOriginal. apply source_membership_block_succ in HB.
   destruct HB as(prefix&newmember&HPrefix&HNew&HAnd).
   destruct(source_cofinal_common_recipe_total M start count Ks)as(old&HOld).
   destruct(code_relation_total M E_cofinal_request(source_cofinal_request_env M member ordinals cover prefix old))as(previous&HPrevious).
   pose proof(IH start Ks Lb seed member ordinals cover prefix old previous HM HO HC HPrefix HOld HPrevious)as PPrevious.
   pose proof(proj1(source_cofinal_request_telescope M member ordinals cover prefix old previous)HPrevious)as HPreviousTel.
   destruct(source_finite_telescope_total M[ordinals;cover;old;newmember]target)as(step&HStep).
   pose proof(source_zfr_cofinal_common_successor M start count Ks Lb old newmember target ordinals cover step HOld HNew HT HO HC HStep)as PStep.
   pose proof(proj1(source_cofinal_request_telescope M member ordinals cover block target result)HResult)as HRT.
   destruct(source_cofinal_frame_bounds M start(succM M count)Ks Lb seed member ordinals cover block target HM HO HC HBOriginal HT)as(k&BA&BT).
   apply(source_zfr_finite_telescope_rule M[previous;step][member;ordinals;cover;block]target result k).
   + intros f[<-|[<-|[]]];assumption.
   + exact BA.
   + exact BT.
   + exact HRT.
   + intros b c n HCtx PK PA.
     pose proof(PA block ltac:(cbn;tauto))as PBlock.
     pose proof(source_full_conjunction_left M b c n prefix newmember block HAnd PBlock)as PPrefix.
     pose proof(source_full_conjunction_right M b c n prefix newmember block HAnd PBlock)as PNew.
     assert(POld:source_full_prv M b c n old).
     { apply(source_full_finite_telescope_apply M[member;ordinals;cover;prefix]old previous HPreviousTel b c n(PK previous ltac:(cbn;tauto))).
       intros f[<-|[<-|[<-|[<-|[]]]]];try exact PPrefix;apply PA;cbn;tauto. }
     apply(source_full_finite_telescope_apply M[ordinals;cover;old;newmember]target step HStep b c n(PK step ltac:(cbn;tauto))).
     intros f[<-|[<-|[<-|[<-|[]]]]];try exact POld;try exact PNew;apply PA;cbn;tauto.
Qed.
Theorem source_zfr_cofinal_common_parameters M start count Ks Lb seed member ordinals cover block target result:
 sf_relation M SFMember seed Ks member ->source_cofinal_ordinals M Ks ordinals ->source_cofinal_cover M Ks Lb cover ->
 source_membership_block M start Lb count block ->source_cofinal_common_recipe M start count Ks target ->
 source_cofinal_request_graph M member ordinals cover block target result ->source_zfr_provable M result.
Proof. exact(source_zfr_cofinal_common_uniform M count start Ks Lb seed member ordinals cover block target result). Qed.
Print Assumptions source_zfr_cofinal_common_uniform.
Print Assumptions source_zfr_cofinal_common_parameters.

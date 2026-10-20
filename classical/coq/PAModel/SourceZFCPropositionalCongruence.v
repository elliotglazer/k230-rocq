From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
  SourcePropositionalTemplates SourceZFCPrograms.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma source_implication_covariance_program A B C D :
  source_prop_program [SPTImpl C A;SPTImpl B D]
    (SPTImpl (SPTImpl A B) (SPTImpl C D)).
Proof.
  apply SPTII,SPTII. apply (SPTIE _ B D).
  - apply SPTCtx. cbn;tauto.
  - apply (SPTIE _ A B).
    + apply SPTCtx. cbn;tauto.
    + apply (SPTIE _ C A);apply SPTCtx;cbn;tauto.
Qed.

Lemma source_conjunction_covariance_program A B C D :
  source_prop_program [SPTImpl A C;SPTImpl B D]
    (SPTImpl (SPTAnd A B) (SPTAnd C D)).
Proof.
  apply SPTII,SPTCI.
  - apply (SPTIE _ A C);[apply SPTCtx;cbn;tauto|].
    apply (SPTCE1 _ A B),SPTCtx. now left.
  - apply (SPTIE _ B D);[apply SPTCtx;cbn;tauto|].
    apply (SPTCE2 _ A B),SPTCtx. now left.
Qed.

Theorem source_zfc_implies_binary M h a b c d f g k :
  (h=SFImpl \/h=SFAnd) ->source_bounded M a k ->source_bounded M b k ->
  source_bounded M c k ->source_bounded M d k ->
  (if match h with SFImpl=>true|_=>false end then source_zfc_implies M c a else source_zfc_implies M a c) ->
  source_zfc_implies M b d ->sf_relation M h a b f ->sf_relation M h c d g ->
  source_zfc_implies M f g.
Proof.
  intros HH HA HB HC HD HP HQ HF HG out HOut.
  set (rho:=code_parameters a b c d).
  assert (HEnv:forall i,source_bounded M (rho i) k).
  { intros [|[|[|i]]];cbn [rho code_parameters];assumption. }
  destruct HH as [EH|EH];subst h.
  - refine (source_zfc_prop_program M _ _
      (source_implication_covariance_program (SPTSlot 0) (SPTSlot 1) (SPTSlot 2) (SPTSlot 3))
      rho k out HEnv _ _).
    + intros p [<-|[<-|[]]] v HV.
      * destruct (source_prop_template_binary M rho SFImpl (SPTSlot 2) (SPTSlot 0) v HV)
          as (x&y&HX&HY&HImpl).
        change (x = c) in HX;change (y = a) in HY;subst x y. exact (HP v HImpl).
      * destruct (source_prop_template_binary M rho SFImpl (SPTSlot 1) (SPTSlot 3) v HV)
          as (x&y&HX&HY&HImpl).
        change (x = b) in HX;change (y = d) in HY;subst x y. exact (HQ v HImpl).
    + apply (source_prop_template_join M rho SFImpl _ _ f g out);[| |exact HOut].
      * exact (source_prop_template_join M rho SFImpl (SPTSlot 0) (SPTSlot 1) a b f eq_refl eq_refl HF).
      * exact (source_prop_template_join M rho SFImpl (SPTSlot 2) (SPTSlot 3) c d g eq_refl eq_refl HG).
  - refine (source_zfc_prop_program M _ _
      (source_conjunction_covariance_program (SPTSlot 0) (SPTSlot 1) (SPTSlot 2) (SPTSlot 3))
      rho k out HEnv _ _).
    + intros p [<-|[<-|[]]] v HV.
      * destruct (source_prop_template_binary M rho SFImpl (SPTSlot 0) (SPTSlot 2) v HV)
          as (x&y&HX&HY&HImpl).
        change (x = a) in HX;change (y = c) in HY;subst x y. exact (HP v HImpl).
      * destruct (source_prop_template_binary M rho SFImpl (SPTSlot 1) (SPTSlot 3) v HV)
          as (x&y&HX&HY&HImpl).
        change (x = b) in HX;change (y = d) in HY;subst x y. exact (HQ v HImpl).
    + apply (source_prop_template_join M rho SFImpl _ _ f g out);[| |exact HOut].
      * exact (source_prop_template_join M rho SFAnd (SPTSlot 0) (SPTSlot 1) a b f eq_refl eq_refl HF).
      * exact (source_prop_template_join M rho SFAnd (SPTSlot 2) (SPTSlot 3) c d g eq_refl eq_refl HG).
Qed.

Theorem source_zfc_equivalent_binary M h a b c d f g k :
  (h=SFImpl \/h=SFAnd) ->source_bounded M a k ->source_bounded M b k ->
  source_bounded M c k ->source_bounded M d k ->
  source_zfc_equivalent M a c ->source_zfc_equivalent M b d ->
  sf_relation M h a b f ->sf_relation M h c d g ->source_zfc_equivalent M f g.
Proof.
  intros HH HA HB HC HD [HAC HCA] [HBD HDB] HF HG. split.
  - apply (source_zfc_implies_binary M h a b c d f g k HH HA HB HC HD);try assumption.
    destruct HH as [EH|EH];subst h;assumption.
  - apply (source_zfc_implies_binary M h c d a b g f k HH HC HD HA HB);try assumption.
    destruct HH as [EH|EH];subst h;assumption.
Qed.

Theorem source_zfc_equivalent_trans M a b c k :
  source_bounded M a k ->source_bounded M b k ->source_bounded M c k ->
  source_zfc_equivalent M a b ->source_zfc_equivalent M b c ->source_zfc_equivalent M a c.
Proof.
  intros HA HB HC [HAB HBA] [HBC HCB].
  assert (Trans:forall x y z,source_bounded M x k ->source_bounded M y k ->source_bounded M z k ->
      source_zfc_implies M x y ->source_zfc_implies M y z ->source_zfc_implies M x z).
  { intros x y z HX HY HZ HXY HYZ out HOut.
    refine (source_zfc_prop_program M
      [SPTImpl (SPTSlot 0) (SPTSlot 1);SPTImpl (SPTSlot 1) (SPTSlot 2)]
      (SPTImpl (SPTSlot 0) (SPTSlot 2)) _ (code_parameters x y z z) k out _ _ _).
    - apply SPTII. apply (SPTIE _ (SPTSlot 1) (SPTSlot 2));[apply SPTCtx;cbn;tauto|].
      apply (SPTIE _ (SPTSlot 0) (SPTSlot 1));apply SPTCtx;cbn;tauto.
    - intros [|[|[|i]]];cbn [code_parameters];assumption.
    - intros p [<-|[<-|[]]] v HV.
      + destruct (source_prop_template_binary M _ SFImpl (SPTSlot 0) (SPTSlot 1) v HV)
          as (u&w&HU&HW&HI).
        change (u=x) in HU;change (w=y) in HW;subst u w. exact (HXY v HI).
      + destruct (source_prop_template_binary M _ SFImpl (SPTSlot 1) (SPTSlot 2) v HV)
          as (u&w&HU&HW&HI).
        change (u=y) in HU;change (w=z) in HW;subst u w. exact (HYZ v HI).
    - exact (source_prop_template_join M _ SFImpl (SPTSlot 0) (SPTSlot 2) x z out eq_refl eq_refl HOut). }
  split;[exact (Trans a b c HA HB HC HAB HBC)|exact (Trans c b a HC HB HA HCB HBA)].
Qed.

Print Assumptions source_zfc_equivalent_binary.
Print Assumptions source_zfc_equivalent_trans.

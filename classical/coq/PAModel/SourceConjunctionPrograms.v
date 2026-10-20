(** Fixed finite source proof programs normalize an encoded conjunction.
    The holes will be arbitrary internal source codes, and the encoded
    falsity slot has an explicit proof that it implies genuine falsity. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition SPTEncodedAnd a b f :=SPTImpl (SPTImpl a (SPTImpl b f)) f.

Theorem source_encoded_conjunction_left Gamma a b f :
  In (SPTEncodedAnd a b f) Gamma ->In (SPTImpl f SPTFalse) Gamma ->
  source_prop_program Gamma a.
Proof.
  intros HE HF. apply (SPTIE Gamma (SPTImpl (SPTImpl a f) a) a);[apply SPTPc|].
  apply SPTII,SPTExp. apply SPTIE with (a:=f).
  - apply SPTCtx. cbn;auto.
  - apply SPTIE with (a:=SPTImpl a (SPTImpl b f)).
    + apply SPTCtx. cbn;auto.
    + apply SPTII,SPTII. apply SPTIE with (a:=a).
      * apply SPTCtx. cbn;auto.
      * apply SPTCtx. cbn;auto.
Qed.

Theorem source_encoded_conjunction_right Gamma a b f :
  In (SPTEncodedAnd a b f) Gamma ->In (SPTImpl f SPTFalse) Gamma ->
  source_prop_program Gamma b.
Proof.
  intros HE HF. apply (SPTIE Gamma (SPTImpl (SPTImpl b f) b) b);[apply SPTPc|].
  apply SPTII,SPTExp. apply SPTIE with (a:=f).
  - apply SPTCtx. cbn;auto.
  - apply SPTIE with (a:=SPTImpl a (SPTImpl b f)).
    + apply SPTCtx. cbn;auto.
    + apply SPTII,SPTII. apply SPTIE with (a:=b).
      * apply SPTCtx. cbn;auto.
      * apply SPTCtx. cbn;auto.
Qed.

Definition source_encoded_conjunction_to_native :=SPTImpl
  (SPTEncodedAnd (SPTSlot 0) (SPTSlot 1) (SPTSlot 2)) (SPTAnd (SPTSlot 0) (SPTSlot 1)).
Definition source_native_conjunction_to_encoded :=SPTImpl
  (SPTAnd (SPTSlot 0) (SPTSlot 1)) (SPTEncodedAnd (SPTSlot 0) (SPTSlot 1) (SPTSlot 2)).

Theorem source_encoded_conjunction_program :
  source_prop_program [SPTImpl (SPTSlot 2) SPTFalse] source_encoded_conjunction_to_native.
Proof.
  unfold source_encoded_conjunction_to_native. apply SPTII,SPTCI.
  - apply (source_encoded_conjunction_left _ _ (SPTSlot 1) (SPTSlot 2));cbn;auto.
  - apply (source_encoded_conjunction_right _ (SPTSlot 0) _ (SPTSlot 2));cbn;auto.
Qed.

Theorem source_native_conjunction_program :
  source_prop_program [] source_native_conjunction_to_encoded.
Proof.
  unfold source_native_conjunction_to_encoded,SPTEncodedAnd. apply SPTII,SPTII.
  apply SPTIE with (a:=SPTSlot 1).
  - apply SPTIE with (a:=SPTSlot 0).
    + apply SPTCtx. cbn;auto.
    + apply SPTCE1 with (b:=SPTSlot 1). apply SPTCtx. cbn;auto.
  - apply SPTCE2 with (a:=SPTSlot 0). apply SPTCtx. cbn;auto.
Qed.

Print Assumptions source_encoded_conjunction_program.
Print Assumptions source_native_conjunction_program.

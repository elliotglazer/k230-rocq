From PAModel Require Import Model FiniteCoding SetFormulaCodes SetCodeDescent SourceBounded
  SourceQuantifierPieceRules SourceQuantifierPieces SourceRelativizationFunctionality.
Unset Implicit Arguments.

Lemma qpiece_binary_inversion M h a b f x y :
  sf_binary h -> sf_relation M h a b f -> qpiece_binary M f x y -> a=x /\ b=y.
Proof.
  intros HH HF [HP|[HP|HP]];
    destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HP) as [EH [EA EB]];
    rewrite (sr_binary_second M h b HH) in EB;exact (conj EA EB).
Qed.
Lemma qpiece_quantifier_inversion M h a f x :
  sf_relation M h a (zeroM M) f -> qpiece_quantifier M f x -> a=x.
Proof.
  intros HF [HP|HP];
    destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HP) as [_ [EA _]];exact EA.
Qed.
Lemma qpiece_binary_quantifier_absurd M h a b f x :
  sf_binary h -> sf_relation M h a b f -> qpiece_quantifier M f x -> False.
Proof.
  intros HH HF [HP|HP];
    destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HP) as [EH _];
    destruct HH as [HH|[HH|HH]];subst h;discriminate.
Qed.
Lemma qpiece_quantifier_binary_absurd M h a f x y :
  (h=SFAll \/ h=SFEx) -> sf_relation M h a (zeroM M) f -> qpiece_binary M f x y -> False.
Proof.
  intros HH HF [HP|[HP|HP]];
    destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HP) as [EH _];
    destruct HH as [HH|HH];subst h;discriminate.
Qed.

Lemma qpiece_child_binary_inv M h a b f n child childn :
  sf_binary h -> sf_relation M h a b f -> qpiece_child M f n child childn ->
  childn=n /\ (child=a \/ child=b).
Proof.
  intros HH HF [[HQ HC]|[sibling [[HP|HP] HC]]].
  - exfalso. exact (qpiece_binary_quantifier_absurd M h a b f child HH HF HQ).
  - destruct (qpiece_binary_inversion M h a b f child sibling HH HF HP) as [HA HB]. auto.
  - destruct (qpiece_binary_inversion M h a b f sibling child HH HF HP) as [HA HB]. auto.
Qed.
Lemma qpiece_child_quantifier_inv M h a f n child childn :
  (h=SFAll \/ h=SFEx) -> sf_relation M h a (zeroM M) f -> qpiece_child M f n child childn ->
  childn=succM M n /\ child=a.
Proof.
  intros HH HF [[HQ HC]|[sibling [[HP|HP] HC]]].
  - split;[exact HC|]. symmetry. exact (qpiece_quantifier_inversion M h a f child HF HQ).
  - exfalso. exact (qpiece_quantifier_binary_absurd M h a f child sibling HH HF HP).
  - exfalso. exact (qpiece_quantifier_binary_absurd M h a f sibling child HH HF HP).
Qed.

Theorem source_quantifier_body_binary M h a b f n k body :
  sf_binary h -> sf_relation M h a b f ->
  (source_quantifier_body M f n k body <->
   source_quantifier_body M a n k body \/ source_quantifier_body M b n k body).
Proof.
  intros HH HF. split.
  - intro H. apply source_quantifier_body_cases in H. destruct H as [[HK HQ]|[child [childn [HC HP]]]].
    + exfalso. exact (qpiece_binary_quantifier_absurd M h a b f body HH HF HQ).
    + destruct (qpiece_child_binary_inv M h a b f n child childn HH HF HC) as [EN [HA|HB]];
        subst childn child;auto.
  - intros [HA|HB].
    + apply (source_quantifier_body_child M f n a n k body);[|exact HA]. right. exists b.
      split;[left;destruct HH as [HH|[HH|HH]];subst h;unfold qpiece_binary;auto|reflexivity].
    + apply (source_quantifier_body_child M f n b n k body);[|exact HB]. right. exists a.
      split;[right;destruct HH as [HH|[HH|HH]];subst h;unfold qpiece_binary;auto|reflexivity].
Qed.
Theorem source_quantifier_body_quantifier M h a f n k body :
  (h=SFAll \/ h=SFEx) -> sf_relation M h a (zeroM M) f ->
  (source_quantifier_body M f n k body <->
   (k=n /\ body=a) \/ source_quantifier_body M a (succM M n) k body).
Proof.
  intros HH HF. split.
  - intro H. apply source_quantifier_body_cases in H. destruct H as [[HK HQ]|[child [childn [HC HP]]]].
    + left. split;[exact HK|]. symmetry. exact (qpiece_quantifier_inversion M h a f body HF HQ).
    + destruct (qpiece_child_quantifier_inv M h a f n child childn HH HF HC) as [EN HA].
      subst childn child. now right.
  - intros [[-> ->]|HP].
    + apply source_quantifier_body_top. destruct HH as [HH|HH];subst h;unfold qpiece_quantifier;auto.
    + apply (source_quantifier_body_child M f n a (succM M n) k body);[|exact HP]. left.
      split;[destruct HH as [HH|HH];subst h;unfold qpiece_quantifier;auto|reflexivity].
Qed.

Lemma qpiece_any_constructor M f n k body : source_quantifier_body M f n k body ->
  exists h a b,sf_relation M h a b f /\ (sf_binary h \/ h=SFAll \/ h=SFEx).
Proof.
  intro H. apply source_quantifier_body_cases in H.
  destruct H as [[_ HQ]|[child [childn [HC HP]]]].
  - destruct HQ as [HQ|HQ].
    + exists SFAll,body,(zeroM M). auto.
    + exists SFEx,body,(zeroM M). auto.
  - destruct HC as [[HQ HN]|[sibling [HB HN]]].
    + destruct HQ as [HQ|HQ].
      * exists SFAll,child,(zeroM M). auto.
      * exists SFEx,child,(zeroM M). auto.
    + destruct HB as [HB|HB];destruct HB as [HB|[HB|HB]];
        first [solve [exists SFAnd,child,sibling;split;[exact HB|left;unfold sf_binary;auto]]
          |solve [exists SFOr,child,sibling;split;[exact HB|left;unfold sf_binary;auto]]
          |solve [exists SFImpl,child,sibling;split;[exact HB|left;unfold sf_binary;auto]]
          |solve [exists SFAnd,sibling,child;split;[exact HB|left;unfold sf_binary;auto]]
          |solve [exists SFOr,sibling,child;split;[exact HB|left;unfold sf_binary;auto]]
          |solve [exists SFImpl,sibling,child;split;[exact HB|left;unfold sf_binary;auto]]].
Qed.

Theorem source_quantifier_body_leaf_none M f n k body :
  (f=zeroM M \/ sf_invalid M f \/ exists h a b,(h=SFMember \/ h=SFEqual) /\ sf_relation M h a b f) ->
  ~source_quantifier_body M f n k body.
Proof.
  intros HF HP. destruct (qpiece_any_constructor M f n k body HP) as (h & a & b & HC & HH).
  destruct HF as [HZ|[HB|[atom [x [y [HA HF]]]]]].
  - exact (sf_relation_nonzero M h a b f HC HZ).
  - exact (sf_invalid_not_constructor M h a b f HB HC).
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HC) as [EH _].
    destruct HA as [HA|HA];subst atom;
      destruct HH as [[HH|[HH|HH]]|[HH|HH]];subst h;discriminate.
Qed.

Print Assumptions source_quantifier_body_binary.
Print Assumptions source_quantifier_body_quantifier.
Print Assumptions source_quantifier_body_leaf_none.

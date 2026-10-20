(** The existing upward-tail renaming is exactly the new substitution when
    the substitution tail base is prefix-length plus delta. This is a
    uniform theorem about arbitrary model-valued source codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalRenamingMaps NumericalRenaming RenamingPayloads
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionPayloads
  SetFormulaCodes SetCodeDescent SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Section MapBridge.
Variable M : Model.
Add Ring renaming_substitution_ring : (model_semiring M).

Theorem renaming_substitution_lookup b c n delta i v :
  renaming_lookup M b c n delta i v <->
  substitution_lookup M b c n (addM M n delta) i v.
Proof.
  split.
  - intros [[Hi Hv]|[Hi Hv]].
    + left. auto.
    + right. split; [exact Hi|].
      destruct (substitution_tail_total M n i Hi) as [j Hj].
      exists j. split; [exact Hj|]. rewrite Hv,Hj. ring.
  - intros [[Hi Hv]|[Hi [j [Hj Hv]]]].
    + left. auto.
    + right. split; [exact Hi|]. rewrite Hj,Hv. ring.
Qed.

Lemma renaming_substitution_lifted_base n m delta : m=succM M n ->
  succM M (addM M n delta) = addM M m delta.
Proof. intro E. rewrite E,Arithmetic.add_succ. reflexivity. Qed.

Theorem renaming_substitution_lift b c n delta d e m :
  renaming_lift M b c n delta d e m <->
  substitution_lift M b c n (addM M n delta) d e m.
Proof.
  split; intros [Em [Hhead Htail]]; split; [exact Em| |exact Em|]; split.
  - rewrite (renaming_substitution_lifted_base n m delta Em).
    apply (proj1 (renaming_substitution_lookup d e m delta _ _)). exact Hhead.
  - intros i v Hv. rewrite (renaming_substitution_lifted_base n m delta Em).
    apply (proj1 (renaming_substitution_lookup d e m delta _ _)).
    apply Htail. apply (proj2 (renaming_substitution_lookup b c n delta _ _)). exact Hv.
  - apply (proj2 (renaming_substitution_lookup d e m delta _ _)).
    rewrite <- (renaming_substitution_lifted_base n m delta Em). exact Hhead.
  - intros i v Hv. apply (proj2 (renaming_substitution_lookup d e m delta _ _)).
    rewrite <- (renaming_substitution_lifted_base n m delta Em).
    apply Htail. apply (proj1 (renaming_substitution_lookup b c n delta _ _)). exact Hv.
Qed.
End MapBridge.

Definition renaming_substitution_at M f :=
  forall b c n delta v, numerical_renaming M f b c n delta v <->
    numerical_substitution M f b c n (addM M n delta) v.

(** Five parameters: b4,c3,n2,delta1,v0; source f remains at5. *)
Definition renaming_substitution_formula : form :=
  ∀∀∀∀∀ ((numerical_renaming_formula $5 $4 $3 $2 $1 $0 →
    numerical_substitution_formula $5 $4 $3 $2 ($2 ⊕ $1) $0) ∧
   (numerical_substitution_formula $5 $4 $3 $2 ($2 ⊕ $1) $0 →
    numerical_renaming_formula $5 $4 $3 $2 $1 $0)).

Local Opaque holds numerical_renaming_formula numerical_substitution_formula.
Lemma renaming_substitution_definable M : Definable1 M (renaming_substitution_at M).
Proof.
  exists renaming_substitution_formula,(fun _ => zeroM M). intro f.
  unfold renaming_substitution_formula,renaming_substitution_at.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_and. setoid_rewrite holds_imp.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  split; intros H b c n delta v; specialize (H b c n delta v); tauto.
Qed.

Lemma renaming_substitution_atom M equality a d f :
  sf_relation M (renaming_source_atom equality) a d f -> renaming_substitution_at M f.
Proof.
  intros Hf b c n delta v.
  assert (Hfs : sf_relation M (substitution_source_atom equality) a d f).
  { destruct equality; exact Hf. }
  rewrite (numerical_renaming_atom M equality a d f b c n delta v Hf),
    (numerical_substitution_atom M equality a d f b c n (addM M n delta) v Hfs).
  setoid_rewrite <- renaming_substitution_lookup.
  destruct equality; reflexivity.
Qed.

Lemma renaming_substitution_binary M h a d f :
  sf_binary h -> sf_relation M h a d f ->
  renaming_substitution_at M a -> renaming_substitution_at M d -> renaming_substitution_at M f.
Proof.
  intros Hh Hf IHa IHd b c n delta v.
  rewrite (numerical_renaming_binary M h a d f b c n delta v Hh Hf),
    (numerical_substitution_binary M h a d f b c n (addM M n delta) v Hh Hf).
  setoid_rewrite (IHa b c n delta). setoid_rewrite (IHd b c n delta). reflexivity.
Qed.

Lemma renaming_substitution_unary M universal a f :
  sf_relation M (renaming_source_quantifier universal) a (zeroM M) f ->
  renaming_substitution_at M a -> renaming_substitution_at M f.
Proof.
  intros Hf IH b c n delta v.
  assert (Hfs : sf_relation M (substitution_source_quantifier universal) a (zeroM M) f).
  { destruct universal; exact Hf. }
  rewrite (numerical_renaming_quantifier M universal a f b c n delta v Hf),
    (numerical_substitution_quantifier M universal a f b c n (addM M n delta) v Hfs).
  split; intros [d [e [m [w [Hlift [Hchild Hout]]]]]]; exists d,e,m,w.
  - split; [apply (proj1 (renaming_substitution_lift M b c n delta d e m)); exact Hlift|].
    split; [|destruct universal; exact Hout].
    rewrite (renaming_substitution_lifted_base M n m delta (proj1 Hlift)).
    apply (proj1 (IH d e m delta w)). exact Hchild.
  - split; [apply (proj2 (renaming_substitution_lift M b c n delta d e m)); exact Hlift|].
    split; [|destruct universal; exact Hout].
    apply (proj2 (IH d e m delta w)).
    rewrite <- (renaming_substitution_lifted_base M n m delta (proj1 Hlift)). exact Hchild.
Qed.

Theorem numerical_renaming_substitution_uniform M f : renaming_substitution_at M f.
Proof.
  revert f. apply (sf_code_induction M (renaming_substitution_at M)).
  - apply renaming_substitution_definable.
  - intros b c n delta v.
    rewrite (numerical_renaming_invalid M (zeroM M) b c n delta v (or_introl eq_refl)),
      (numerical_substitution_invalid M (zeroM M) b c n (addM M n delta) v (or_introl eq_refl)).
    reflexivity.
  - intros f Hbad b c n delta v.
    rewrite (numerical_renaming_invalid M f b c n delta v (or_intror Hbad)),
      (numerical_substitution_invalid M f b c n (addM M n delta) v (or_intror Hbad)).
    reflexivity.
  - intros a d f Hf. exact (renaming_substitution_atom M false a d f Hf).
  - intros a d f Hf. exact (renaming_substitution_atom M true a d f Hf).
  - exact (renaming_substitution_binary M).
  - intros h a f Hh Hf IH. destruct Hh as [Hh|Hh]; subst h.
    + exact (renaming_substitution_unary M true a f Hf IH).
    + exact (renaming_substitution_unary M false a f Hf IH).
Qed.

Corollary numerical_renaming_substitution M f b c n delta v :
  numerical_renaming M f b c n delta v <->
  numerical_substitution M f b c n (addM M n delta) v.
Proof. exact (numerical_renaming_substitution_uniform M f b c n delta v). Qed.

Corollary numerical_renaming_empty_substitution M f b c delta v :
  numerical_renaming M f b c (zeroM M) delta v <->
  numerical_substitution M f b c (zeroM M) delta v.
Proof.
  pose proof (numerical_renaming_substitution M f b c (zeroM M) delta v) as H.
  now rewrite Arithmetic.add_zero in H.
Qed.

Lemma renaming_substitution_formula_bound : bounded 1 renaming_substitution_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions renaming_substitution_lookup.
Print Assumptions renaming_substitution_lift.
Print Assumptions renaming_substitution_definable.
Print Assumptions numerical_renaming_substitution_uniform.
Print Assumptions numerical_renaming_substitution.
Print Assumptions numerical_renaming_empty_substitution.
Print Assumptions renaming_substitution_formula_bound.

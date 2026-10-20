(** A named binder followed by a lifted scope map equals extending the
    scope stack. This is the actual renaming square for arbitrary matrices;
    repeated binder names are allowed. *)
From Stdlib Require Import List.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalRenamingMaps NumericalRenaming SourceBounded SourceRenamingBounds
  SourceRenamingIdentity SourceShiftSpecialization SourceRenamingDiamond RawBinderRenaming
  SourceNamedScopes.
Import ListNotations.
Unset Implicit Arguments.

Definition named_scope_renaming M names f g :=exists rb rc,
  named_scope_map M names rb rc /\
  numerical_renaming M f rb rc (named_scope_bound M names) (code_numeral M (length names)) g.

Theorem named_scope_renaming_total M names f :exists g,named_scope_renaming M names f g.
Proof.
  destruct (named_scope_map_total M names) as (rb&rc&HM).
  destruct (numerical_renaming_total M f rb rc (named_scope_bound M names)
    (code_numeral M (length names))) as (g&HG).
  exists g,rb,rc. auto.
Qed.

Theorem named_scope_renaming_bounded M names f g k :
  source_bounded M f k ->named_scope_renaming M names f g ->
  source_bounded M g (named_scope_succ M (length names) k).
Proof.
  intros HF (rb&rc&HM&HR).
  apply (numerical_renaming_preserves_bound M f rb rc (named_scope_bound M names)
    (code_numeral M (length names)) g k _ HF HR).
  intros i j HI HJ. apply HM in HJ. exact (named_scope_index_bounded M names i j k HI HJ).
Qed.

Theorem named_scope_renaming_functional M names f g h :
  named_scope_renaming M names f g ->named_scope_renaming M names f h ->g=h.
Proof.
  intros (rb&rc&HM&HR)(sb&sc&HN&HS).
  apply (numerical_renaming_functional_equivalent M f rb rc (named_scope_bound M names)
    sb sc (named_scope_bound M names) (code_numeral M (length names)) g h);[|exact HR|exact HS].
  intros i v. rewrite (HM i v),(HN i v). reflexivity.
Qed.

Theorem named_scope_renaming_empty M f g k :
  source_bounded M f k ->named_scope_renaming M [] f g ->g=f.
Proof.
  intros HF (rb&rc&HM&HR). symmetry.
  apply (numerical_renaming_functional M f rb rc (named_scope_bound M [])
    (zeroM M) f g);[|exact HR].
  apply (numerical_renaming_identity_on_bound M f rb rc _ _ k HF).
  intros i _. apply HM. reflexivity.
Qed.

Theorem named_scope_bind_lift M names x f closed target rb rc ab ac db dc dn cb cc k :
  source_bounded M f k ->named_scope_map M names rb rc ->
  raw_binder_renaming M x ab ac ->
  numerical_renaming M f ab ac (succM M x) (code_numeral M 1) closed ->
  renaming_lift M rb rc (named_scope_bound M names) (code_numeral M (length names)) db dc dn ->
  named_scope_map M (x::names) cb cc ->
  numerical_renaming M f cb cc (named_scope_bound M (x::names))
    (code_numeral M (length (x::names))) target ->
  numerical_renaming M closed db dc dn (code_numeral M (length names)) target.
Proof.
  intros HF HM HX HC HL HN HT.
  destruct (numerical_renaming_total M closed db dc dn (code_numeral M (length names))) as (actual&HA).
  assert (HId:numerical_renaming M target (zeroM M) (zeroM M) (zeroM M) (zeroM M) actual).
  { apply (numerical_source_renaming_diamond M f k ab ac (succM M x) (code_numeral M 1)
      cb cc (named_scope_bound M (x::names)) (code_numeral M (length (x::names)))
      db dc dn (code_numeral M (length names)) (zeroM M) (zeroM M) (zeroM M) (zeroM M)
      closed target actual HF HC HT HA).
    intros i j l v _ HJ HV HI.
    apply HX in HJ. apply HN in HI.
    assert (E:v=l).
    { destruct HJ as [[-> ->]|[NE ->]].
      - apply (proj1 (renaming_lift_head M rb rc _ _ db dc dn v HL)) in HV.
        cbn [named_scope_index] in HI. destruct HI as [[_ E]|[NE' _]];congruence.
      - destruct (renaming_lift_tail_inv M rb rc _ _ db dc dn i v HL HV) as (w&HW&EV).
        apply HM in HW. cbn [named_scope_index] in HI.
        destruct HI as [[EQ _]|[_ (u&HU&EL)]];[contradiction|].
        pose proof (named_scope_index_functional M names i w u HW HU) as EU. congruence. }
    subst v. apply source_empty_renaming_lookup. }
  assert (HTB:source_bounded M target (named_scope_succ M (length (x::names)) k)).
  { apply (named_scope_renaming_bounded M (x::names) f target k HF). exists cb,cc. auto. }
  assert (HE:numerical_renaming M target (zeroM M) (zeroM M) (zeroM M) (zeroM M) target).
  { apply (numerical_renaming_identity_on_bound M target _ _ _ _ _ HTB).
    intros i _. apply source_empty_renaming_lookup. }
  assert (actual = target) by (eapply numerical_renaming_functional;[exact HId|exact HE]).
  now subst actual.
Qed.

Print Assumptions named_scope_renaming_total.
Print Assumptions named_scope_bind_lift.

Theorem named_scope_renaming_at M names f g rb rc :
  named_scope_renaming M names f g ->named_scope_map M names rb rc ->
  numerical_renaming M f rb rc (named_scope_bound M names) (code_numeral M (length names)) g.
Proof.
  intros (sb&sc&HS&HG) HR.
  assert (HE:renaming_equivalent M sb sc (named_scope_bound M names)
      rb rc (named_scope_bound M names) (code_numeral M (length names))).
  { intros i v. rewrite (HS i v),(HR i v). reflexivity. }
  exact (proj1 (numerical_renaming_extensional M f sb sc (named_scope_bound M names)
    rb rc (named_scope_bound M names) (code_numeral M (length names)) g HE) HG).
Qed.

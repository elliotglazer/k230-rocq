(** Standard-source calibration of the internally certified renaming.
    This identifies the concrete descriptor transformations with minZF's
    actual capture-avoiding de Bruijn substitutions. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SetCodeDescent StandardModel NumericalRenamingMaps
  RenamingPayloads NumericalRenaming SchemaRenamingDescriptors SetSchemaConstructors.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma rename_vector_hd_map {A B n} (f:A->B) (v:Vector.t A (S n)) :
  Vector.hd (Vector.map f v)=f (Vector.hd v).
Proof.
  refine (Vector.caseS' v (fun w => Vector.hd (Vector.map f w)=f (Vector.hd w)) _).
  intros h t. reflexivity.
Qed.
Lemma rename_vector_tl_map {A B n} (f:A->B) (v:Vector.t A (S n)) :
  Vector.tl (Vector.map f v)=Vector.map f (Vector.tl v).
Proof.
  refine (Vector.caseS' v (fun w => Vector.tl (Vector.map f w)=Vector.map f (Vector.tl w)) _).
  intros h t. reflexivity.
Qed.
Lemma rename_index_subst (sigma:nat->sf_term) (t:sf_term) :
  sf_index t`[sigma]=sf_index (sigma (sf_index t)).
Proof. destruct t as [i|[]]. reflexivity. Qed.

Lemma sf_make_graph h a b : sf_relation natModel h a b (sf_make h a b).
Proof. unfold sf_relation. rewrite code_relation_natModel. reflexivity. Qed.

Lemma rename_vector2_eta {A} (v:Vector.t A 2) :
  v=Vector.cons A (Vector.hd v) 1
    (Vector.cons A (Vector.hd (Vector.tl v)) 0 (Vector.nil A)).
Proof.
  refine (Vector.caseS' v (fun w => w=Vector.cons A (Vector.hd w) 1
    (Vector.cons A (Vector.hd (Vector.tl w)) 0 (Vector.nil A))) _).
  intros a t. refine (Vector.caseS' t (fun w => Vector.cons A a 1 w=
    Vector.cons A a 1 (Vector.cons A (Vector.hd w) 0 (Vector.nil A))) _).
  intros z e. now rewrite (Vector.case0 (fun w => w=Vector.nil A) eq_refl e).
Qed.
Theorem numerical_renaming_source_calibration (phi:sf_form) :
  forall b c n delta (sigma:nat->sf_term),
  (forall i, renaming_lookup natModel b c n delta i (sf_index (sigma i))) ->
  numerical_renaming natModel (sf_encode phi) b c n delta (sf_encode phi[sigma]).
Proof.
  induction phi as [|ff P t|ff op phi1 IHphi1 phi2 IHphi2|ff q phi IHphi]; intros b c n delta sigma Hmap.
  - apply numerical_renaming_invalid; [now left|reflexivity].
  - destruct P; change (Vector.t sf_term 2) in t; rewrite (rename_vector2_eta t); cbn [subst_form sf_encode Vector.map Vector.hd Vector.tl Vector.caseS Vector.caseS']; repeat rewrite rename_index_subst.
    + apply (proj2 (numerical_renaming_member natModel _ _ _ b c n delta _ (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply Hmap|]. split; [apply Hmap|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_equal natModel _ _ _ b c n delta _ (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply Hmap|]. split; [apply Hmap|apply sf_make_graph].
  - cbn [subst_form sf_encode].
    destruct op.
    + apply (proj2 (numerical_renaming_binary natModel SFAnd _ _ _ b c n delta _
        (or_introl eq_refl) (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply IHphi1;exact Hmap|].
      split; [apply IHphi2;exact Hmap|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_binary natModel SFOr _ _ _ b c n delta _
        (or_intror (or_introl eq_refl)) (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply IHphi1;exact Hmap|].
      split; [apply IHphi2;exact Hmap|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_binary natModel SFImpl _ _ _ b c n delta _
        (or_intror (or_intror eq_refl)) (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply IHphi1;exact Hmap|].
      split; [apply IHphi2;exact Hmap|apply sf_make_graph].
  - destruct (renaming_lift_total natModel b c n delta) as [d [e [m Hlift]]].
    assert (Hup : forall i, renaming_lookup natModel d e m delta i (sf_index (up sigma i))).
    { intros [|i]; rewrite source_up_substitution_index.
      - apply (proj2 (renaming_lift_head natModel b c n delta d e m 0 Hlift)). reflexivity.
      - apply (proj2 (renaming_lift_tail natModel b c n delta d e m i _ Hlift)). apply Hmap. }
    cbn [subst_form sf_encode]. destruct q.
    + apply (proj2 (numerical_renaming_quantifier natModel true _ _ b c n delta _ (sf_make_graph _ _ _))).
      exists d,e,m,(sf_encode phi[up sigma]). split; [exact Hlift|].
      split; [apply IHphi;exact Hup|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_quantifier natModel false _ _ b c n delta _ (sf_make_graph _ _ _))).
      exists d,e,m,(sf_encode phi[up sigma]). split; [exact Hlift|].
      split; [apply IHphi;exact Hup|apply sf_make_graph].
Qed.

Definition schema_substitution s : nat->sf_term :=
  match s with SepBody=>sep_substitution | RepA=>rep_substitution_A |
    RepB=>rep_substitution_B | RepC=>rep_substitution_C end.

Lemma schema_descriptor_standard s i :
  schema_lookup natModel s i (sf_index (schema_substitution s i)).
Proof.
  destruct i as [|[|i]].
  - apply schema_lookup_first. destruct s; reflexivity.
  - apply schema_lookup_second. destruct s; reflexivity.
  - apply schema_lookup_tail.
    + unfold coding_lt. cbn [natModel raw_interpretation].
      rewrite numeral_natModel. destruct s; cbn; intros [d H]; lia.
    + change (sf_index (schema_substitution s (S(S i)))=
        S(S i)+code_numeral natModel (schema_delta s)).
      rewrite numeral_natModel. destruct s; cbn; lia.
Qed.

Theorem schema_renaming_source_calibration s (phi:sf_form) :
  schema_renaming natModel s (sf_encode phi) (sf_encode phi[schema_substitution s]).
Proof. apply numerical_renaming_source_calibration. apply schema_descriptor_standard. Qed.
Theorem schema_renaming_standard_iff s (phi:sf_form) body :
  schema_renaming natModel s (sf_encode phi) body <->
  body=sf_encode phi[schema_substitution s].
Proof.
  split.
  - intro H. eapply schema_renaming_functional; [exact H|apply schema_renaming_source_calibration].
  - intros ->. apply schema_renaming_source_calibration.
Qed.

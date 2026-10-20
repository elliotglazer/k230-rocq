(** An internal Hilbert-proof induction, conditional on explicit source
    axiom images and closure rules. These premises are not established here. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent NumericalProofs
  NumericalTheories TheoryProofInduction NumericalEnvironments SetFormulaCodes NumericalRenaming RawBinderRenaming
  RawSourceImage RawSourceImageInversion RawSourcePropositional.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition raw_image_property M (Q:carrier M->Prop) f :=
  forall s,raw_source_image M f s -> Q s.
Definition raw_image_property_formula (theta:form) : form :=
  ∀ (raw_source_image_formula $1 $0 → theta[($0 .: fun i => var (2+i))]).
Local Opaque raw_source_image_formula.
Theorem raw_image_property_definable M Q : Definable1 M Q ->
  Definable1 M (raw_image_property M Q).
Proof.
  intros [theta [rho HQ]]. exists (raw_image_property_formula theta),rho. intro f.
  unfold raw_image_property_formula,raw_image_property.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite raw_source_image_formula_correct.
  assert (HE:forall s,holds M (s .: f .: rho) (theta[($0 .: fun i => var (2+i))]) <-> Q s).
  { intro s. rewrite (HQ s). unfold holds. rewrite sat_comp.
    apply sat_ext. intros [|i];reflexivity. }
  setoid_rewrite HE. reflexivity.
Qed.

Definition raw_axiom_images M (Q:carrier M->Prop) :=
  forall f s,K230_axiom_relation M f -> raw_source_image M f s -> Q s.
Definition raw_named_generalization_closure M (Q:carrier M->Prop) :=
  forall s x b c v out,Q s -> raw_binder_renaming M x b c ->
    numerical_renaming M s b c (succM M x) (succM M (zeroM M)) v ->
    sf_relation M SFAll v (zeroM M) out -> Q out.

Theorem raw_source_proof_transfer M Q :
  Definable1 M Q ->
  (forall s,sf_relation M SFImpl (zeroM M) (zeroM M) s -> Q s) ->
  (forall a b h,Q a -> Q h -> sf_relation M SFImpl a b h -> Q b) ->
  raw_named_generalization_closure M Q -> raw_axiom_images M Q ->
  forall f,numerically_provable M f -> raw_image_property M Q f.
Proof.
  intros HD HT HM HG HA f HP. apply (theory_proof_induction M K230Theory (raw_image_property M Q)).
  - exact (raw_image_property_definable M Q HD).
  - intros g Hax s HS. exact (HA g s (proj1 (K230Theory_axiom M g) Hax) HS).
  - intros a b h HPa HPh HI s HS.
    destruct (environment_lt_cases M (zeroM M) h) as [Hpos|Hn].
    + assert (HN:h<>zeroM M).
      { intro E. subst h. exact (coding_not_lt_zero M _ Hpos). }
      destruct (raw_source_image_total M h) as [sh Hsh].
      destruct (raw_source_implication_inv M a b h sh HN HI Hsh) as (u&v&HU&HV&HImpl).
      rewrite (raw_source_image_functional M b v s HV HS) in HImpl.
      exact (HM u s sh (HPa u HU) (HPh sh Hsh) HImpl).
    + assert (E:h=zeroM M).
      { destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
          (fun ax H rho=>axioms M ax rho H) h) as [E|[u E]];[exact E|].
        subst h. exfalso. exact (Hn (coding_zero_lt_succ M u)). }
      subst h. destruct (raw_zero_implication_arguments M a b HI) as [_ ->].
      exact (HT s (raw_source_zero_inv M s HS)).
  - intros x g out HPG HU s HS.
    destruct (raw_source_universal_inv M x g out s HU HS) as (v&b&c&w&HV&HB&HR&HAll).
    exact (HG v x b c w s (HPG v HV) HB HR HAll).
  - exact (proj2 (K230Theory_provable M f) HP).
Qed.

Print Assumptions raw_image_property_definable.
Print Assumptions raw_source_proof_transfer.

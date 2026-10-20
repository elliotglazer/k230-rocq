(** Inversion and uniqueness for the internal raw-to-source computation.
    The degenerate raw implication 0=(0->0) remains a separate truth case. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing CodeExpressions
  CodeDescent CodeTags NumericalProofs NumericalTraces SetFormulaCodes NumericalRenaming
  RawBinderRenaming RawSourceImage.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem raw_source_image_cases M f s : raw_source_image M f s ->
  raw_source_base M f s \/
  (exists x g u b c v, universal_graph M x g f /\ raw_source_image M g u /\
    raw_binder_renaming M x b c /\
    numerical_renaming M u b c (succM M x) (succM M (zeroM M)) v /\
    sf_relation M SFAll v (zeroM M) s) \/
  (exists a b u v, f<>zeroM M /\ implication_graph M a b f /\
    raw_source_image M a u /\ raw_source_image M b v /\ sf_relation M SFImpl u v s).
Proof.
  intros [row [Hrow HD]]. destruct (trace_derives_inv M raw_source_rules row HD) as [HB|[HU|HB]].
  - apply raw_source_trace_base in HB. destruct HB as [ff [ss [HP HB]]].
    destruct (pair_injective M row f s ff ss Hrow HP) as [<- <-]. now left.
  - destruct HU as [previous [DP HU]]. apply raw_source_trace_unary in HU.
    destruct HU as (ff&ss&x&g&u&b&c&v&HP&HG&HF&HMap&HR&HS).
    destruct (pair_injective M row f s ff ss Hrow HP) as [<- <-].
    right;left. exists x,g,u,b,c,v. repeat first [assumption|split]. exists previous;auto.
  - destruct HB as [left [right [DL [DR HB]]]]. apply raw_source_trace_binary in HB.
    destruct HB as (ff&ss&a&b&u&v&HP&HA&HB&HN&HI&HS).
    destruct (pair_injective M row f s ff ss Hrow HP) as [<- <-].
    right;right. exists a,b,u,v. repeat first [assumption|split].
    + exists left;auto.
    + exists right;auto.
Qed.

Lemma raw_positive_tag_nonzero M tag a b f :
  tag<>0 -> tagged_pair_graph M tag a b f -> f<>zeroM M.
Proof.
  intros Htag HF ->. destruct (tagged_pair_positive_descent M a b (zeroM M) tag Htag HF) as [HA _].
  exact (coding_not_lt_zero M a HA).
Qed.

Theorem raw_source_zero_inv M s : raw_source_image M (zeroM M) s ->
  sf_relation M SFImpl (zeroM M) (zeroM M) s.
Proof.
  intro H. apply raw_source_image_cases in H. destruct H as [H|[H|H]].
  - destruct H as [[_ HS]|[[a [b [HM _]]]|[a [b [HE _]]]]];[exact HS| |].
    + contradiction (raw_positive_tag_nonzero M 1 a b (zeroM M) ltac:(lia) HM eq_refl).
    + contradiction (raw_positive_tag_nonzero M 3 a b (zeroM M) ltac:(lia) HE eq_refl).
  - destruct H as (x&g&u&b&c&v&HF&_). apply universal_graph_tagged in HF.
    contradiction (raw_positive_tag_nonzero M 2 x g (zeroM M) ltac:(lia) HF eq_refl).
  - destruct H as (a&b&u&v&HN&_). contradiction.
Qed.

Theorem raw_source_member_inv M a b f s : membership_graph M a b f ->
  raw_source_image M f s -> sf_relation M SFMember a b s.
Proof.
  intros HF H. apply raw_source_image_cases in H. destruct H as [H|[H|H]].
  - destruct H as [[E _]|[[a' [b' [HM HS]]]|[a' [b' [HE _]]]]].
    + subst f. contradiction (raw_positive_tag_nonzero M 1 a b (zeroM M) ltac:(lia) HF eq_refl).
    + destruct (tagged_pair_decode_unique M 1 1 a b a' b' f ltac:(lia) ltac:(lia) HF HM) as [_ [<- <-]]. exact HS.
    + destruct (tagged_pair_decode_unique M 1 3 a b a' b' f ltac:(lia) ltac:(lia) HF HE) as [E _]. discriminate E.
  - destruct H as (x&g&u&bb&c&v&HG&_). apply universal_graph_tagged in HG.
    destruct (tagged_pair_decode_unique M 1 2 a b x g f ltac:(lia) ltac:(lia) HF HG) as [E _]. discriminate E.
  - destruct H as (aa&bb&u&v&_&HI&_). apply implication_graph_tagged in HI.
    destruct (tagged_pair_decode_unique M 1 0 a b aa bb f ltac:(lia) ltac:(lia) HF HI) as [E _]. discriminate E.
Qed.

Theorem raw_source_equal_inv M a b f s : equality_graph M a b f ->
  raw_source_image M f s -> sf_relation M SFEqual a b s.
Proof.
  intros HF H. apply raw_source_image_cases in H. destruct H as [H|[H|H]].
  - destruct H as [[E _]|[[a' [b' [HM _]]]|[a' [b' [HE HS]]]]].
    + subst f. contradiction (raw_positive_tag_nonzero M 3 a b (zeroM M) ltac:(lia) HF eq_refl).
    + destruct (tagged_pair_decode_unique M 3 1 a b a' b' f ltac:(lia) ltac:(lia) HF HM) as [E _]. discriminate E.
    + destruct (tagged_pair_decode_unique M 3 3 a b a' b' f ltac:(lia) ltac:(lia) HF HE) as [_ [<- <-]]. exact HS.
  - destruct H as (x&g&u&bb&c&v&HG&_). apply universal_graph_tagged in HG.
    destruct (tagged_pair_decode_unique M 3 2 a b x g f ltac:(lia) ltac:(lia) HF HG) as [E _]. discriminate E.
  - destruct H as (aa&bb&u&v&_&HI&_). apply implication_graph_tagged in HI.
    destruct (tagged_pair_decode_unique M 3 0 a b aa bb f ltac:(lia) ltac:(lia) HF HI) as [E _]. discriminate E.
Qed.

Theorem raw_source_implication_inv M a b f s : f<>zeroM M -> implication_graph M a b f ->
  raw_source_image M f s -> exists u v,raw_source_image M a u /\ raw_source_image M b v /\ sf_relation M SFImpl u v s.
Proof.
  intros HN HF H. apply implication_graph_tagged in HF.
  apply raw_source_image_cases in H. destruct H as [H|[H|H]].
  - destruct H as [[E _]|[[a' [b' [HM _]]]|[a' [b' [HE _]]]]].
    + contradiction.
    + destruct (tagged_pair_decode_unique M 0 1 a b a' b' f ltac:(lia) ltac:(lia) HF HM) as [E _]. discriminate E.
    + destruct (tagged_pair_decode_unique M 0 3 a b a' b' f ltac:(lia) ltac:(lia) HF HE) as [E _]. discriminate E.
  - destruct H as (x&g&u&bb&c&v&HG&_). apply universal_graph_tagged in HG.
    destruct (tagged_pair_decode_unique M 0 2 a b x g f ltac:(lia) ltac:(lia) HF HG) as [E _]. discriminate E.
  - destruct H as (aa&bb&u&v&_&HI&HA&HB&HS). apply implication_graph_tagged in HI.
    destruct (tagged_pair_decode_unique M 0 0 a b aa bb f ltac:(lia) ltac:(lia) HF HI) as [_ [<- <-]].
    exists u,v. auto.
Qed.

Theorem raw_source_universal_inv M x g f s : universal_graph M x g f -> raw_source_image M f s ->
  exists u b c v,raw_source_image M g u /\ raw_binder_renaming M x b c /\
    numerical_renaming M u b c (succM M x) (succM M (zeroM M)) v /\ sf_relation M SFAll v (zeroM M) s.
Proof.
  intros HF H. apply universal_graph_tagged in HF.
  apply raw_source_image_cases in H. destruct H as [H|[H|H]].
  - destruct H as [[E _]|[[a' [b' [HM _]]]|[a' [b' [HE _]]]]].
    + subst f. contradiction (raw_positive_tag_nonzero M 2 x g (zeroM M) ltac:(lia) HF eq_refl).
    + destruct (tagged_pair_decode_unique M 2 1 x g a' b' f ltac:(lia) ltac:(lia) HF HM) as [E _]. discriminate E.
    + destruct (tagged_pair_decode_unique M 2 3 x g a' b' f ltac:(lia) ltac:(lia) HF HE) as [E _]. discriminate E.
  - destruct H as (xx&gg&u&b&c&v&HG&HU&HMap&HR&HS). apply universal_graph_tagged in HG.
    destruct (tagged_pair_decode_unique M 2 2 x g xx gg f ltac:(lia) ltac:(lia) HF HG) as [_ [<- <-]].
    exists u,b,c,v. repeat first [assumption|split].
  - destruct H as (aa&bb&u&v&_&HI&_). apply implication_graph_tagged in HI.
    destruct (tagged_pair_decode_unique M 2 0 x g aa bb f ltac:(lia) ltac:(lia) HF HI) as [E _]. discriminate E.
Qed.

Local Opaque holds raw_source_image_formula.
Lemma raw_source_functionality_definable M :
  Definable1 M (fun f=>forall s t,raw_source_image M f s -> raw_source_image M f t -> s=t).
Proof.
  exists (∀∀ (raw_source_image_formula $2 $1 → (raw_source_image_formula $2 $0 → $1 == $0))),
    (fun _=>zeroM M).
  intro f. repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite raw_source_image_formula_correct. reflexivity.
Qed.

Theorem raw_source_image_functional M f s t :
  raw_source_image M f s -> raw_source_image M f t -> s=t.
Proof.
  revert f s t. apply (named_formula_code_induction M
    (fun f=>forall s t,raw_source_image M f s -> raw_source_image M f t -> s=t)).
  - apply raw_source_functionality_definable.
  - intros s t HS HT. exact (sf_relation_functional M SFImpl (zeroM M) (zeroM M) s t
      (raw_source_zero_inv M s HS) (raw_source_zero_inv M t HT)).
  - intros a b f HF s t HS HT. exact (sf_relation_functional M SFMember a b s t
      (raw_source_member_inv M a b f s HF HS) (raw_source_member_inv M a b f t HF HT)).
  - intros a b f HF s t HS HT. exact (sf_relation_functional M SFEqual a b s t
      (raw_source_equal_inv M a b f s HF HS) (raw_source_equal_inv M a b f t HF HT)).
  - intros a b f HN HF IHa IHb s t HS HT.
    destruct (raw_source_implication_inv M a b f s HN HF HS) as (u&v&HU&HV&SF).
    destruct (raw_source_implication_inv M a b f t HN HF HT) as (uu&vv&HUU&HVV&TF).
    assert (u=uu) by exact (IHa u uu HU HUU). assert (v=vv) by exact (IHb v vv HV HVV).
    subst uu vv. exact (sf_relation_functional M SFImpl u v s t SF TF).
  - intros x g f HF IH s t HS HT.
    destruct (raw_source_universal_inv M x g f s HF HS) as (u&b&c&v&HU&HB&HR&SF).
    destruct (raw_source_universal_inv M x g f t HF HT) as (uu&bb&cc&vv&HUU&HBB&HRR&TF).
    assert (u=uu) by exact (IH u uu HU HUU). subst uu.
    assert (v=vv).
    { exact (numerical_renaming_functional_equivalent M u b c (succM M x) bb cc (succM M x)
        (succM M (zeroM M)) v vv (raw_binder_renaming_equivalent M x b c bb cc HB HBB) HR HRR). }
    subst vv. exact (sf_relation_functional M SFAll v (zeroM M) s t SF TF).
Qed.

Print Assumptions raw_source_image_cases.
Print Assumptions raw_source_implication_inv.
Print Assumptions raw_source_universal_inv.
Print Assumptions raw_source_image_functional.

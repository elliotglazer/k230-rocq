(** Uniform finite collection of the target contexts used by source axiom
    images. PA induction, not a host finite list or a choice principle, combines them. *)
From PAModel Require Import Model CodeExpressions FiniteCoding FiniteCRT FiniteCRTFormula NumericalProofs
  NumericalTheories NumericalContexts NumericalSourceFull SourceRelativization
  SourceRelativizationFunctionality SourceProofWeakening ContextCombination
  SourceAxiomContexts SourceContextImages.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_image_context_collection_at M T domain b c n k :=
  coding_lt M k (succM M n) -> exists tb tc tn,
    source_axiom_context M T tb tc tn /\ source_context_images M domain b c k tb tc tn.
Definition source_image_context_collection_formula T : form :=
  Peano.sless $0 (σ $3) → ∃∃∃ (source_axiom_context_formula T $2 $1 $0 ∧
    source_context_images_formula $7 $4 $5 $3 $2 $1 $0).
Local Opaque holds Peano.sless source_axiom_context_formula source_context_images_formula.

Theorem source_image_context_collection_definable M T domain b c n :
  Definable1 M (source_image_context_collection_at M T domain b c n).
Proof.
  exists (source_image_context_collection_formula T),(b .: c .: n .: domain .: fun _=>zeroM M). intro k.
  unfold source_image_context_collection_formula,source_image_context_collection_at.
  rewrite holds_imp. repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite holds_sless. setoid_rewrite source_axiom_context_formula_correct.
  setoid_rewrite source_context_images_formula_correct. reflexivity.
Qed.

Theorem source_axiom_image_context_collect M T domain b c n :
  (forall f g,context_member M b c n f -> source_relativization M domain f g ->
    exists tb tc tn,source_axiom_context M T tb tc tn /\ source_full_prv M tb tc tn g) ->
  exists tb tc tn,source_axiom_context M T tb tc tn /\ source_context_images M domain b c n tb tc tn.
Proof.
  intro HLocal.
  assert (HAll:forall k,source_image_context_collection_at M T domain b c n k).
  { apply (definable_induction M (source_image_context_collection_at M T domain b c n)
      (source_image_context_collection_definable M T domain b c n)).
    - intros _. exists (zeroM M),(zeroM M),(zeroM M). split.
      + exact (source_axiom_context_empty M T).
      + intros f g HF _. exfalso. exact (context_empty M b c f HF).
    - intros k IH HKn.
      pose proof (proj1 (coding_lt_succ_cancel M k n) HKn) as HK.
      assert (HKle:coding_lt M k (succM M n)).
      { apply (proj2 (coding_lt_succ_cases M k n)). now left. }
      destruct (IH HKle) as (tb & tc & tn & HOld & HImages).
      destruct (beta_total M b c k) as [f HF].
      destruct (source_relativization_total M domain f) as [g HG].
      destruct (HLocal f g (ex_intro _ k (conj HK HF)) HG) as (db & dc & dn & HNew & PNew).
      destruct (context_union_total M tb tc tn db dc dn) as (ub & uc & un & HU).
      pose proof (source_axiom_context_union M T tb tc tn db dc dn ub uc un HOld HNew HU) as HUnion.
      exists ub,uc,un. split;[exact HUnion|].
      intros a ar [i [HI HA]] HAR.
      destruct (proj1 (coding_lt_succ_cases M i k) HI) as [HIk|E].
      + apply (source_full_prv_weaken_bounded M tb tc tn ub uc un ar (zeroM M));[| |exact (proj1 HUnion)].
        * exact (HImages a ar (ex_intro _ i (conj HIk HA)) HAR).
        * exact (context_union_left M tb tc tn db dc dn ub uc un HU).
      + subst i.
        pose proof (beta_unique M b c k a f HA HF) as E. subst a.
        pose proof (source_relativization_functional M f domain ar g HAR HG) as E. subst ar.
        apply (source_full_prv_weaken_bounded M db dc dn ub uc un g (zeroM M) PNew);[|exact (proj1 HUnion)].
        exact (context_union_right M tb tc tn db dc dn ub uc un HU). }
  exact (HAll n (coding_lt_succ M n)).
Qed.

Print Assumptions source_image_context_collection_definable.
Print Assumptions source_axiom_image_context_collect.

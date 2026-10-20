(** A genuinely internally finite family of descriptor proofs shares an
    actual axiom context. The induction length may be nonstandard. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  NumericalContexts NumericalSourceFull SourceAxiomContexts SourceDescriptorProvability
  ContextCombination SourceProofWeakening.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.

Definition source_internal_proof_context_at M T sb sc N k:=
  coding_lt M k(succM M N) ->exists b c n,
    source_axiom_context M T b c n /\
    forall f,context_member M sb sc k f ->source_full_prv M b c n f.
Definition source_internal_proof_context_formula T:form:=
  Peano.sless $0 (σ $3) →∃∃∃(source_axiom_context_formula T $2 $1 $0 ∧
    ∀(context_member_formula $5 $6 $4 $0 →source_full_prv_formula $3 $2 $1 $0)).
Local Opaque holds Peano.sless source_axiom_context_formula context_member_formula source_full_prv_formula.

Theorem source_internal_proof_context_definable M T sb sc N:
  Definable1 M(source_internal_proof_context_at M T sb sc N).
Proof.
  exists(source_internal_proof_context_formula T),(sb .: sc .: N .: fun _=>zeroM M). intro k.
  unfold source_internal_proof_context_formula,source_internal_proof_context_at.
  rewrite holds_imp. repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite source_axiom_context_formula_correct.
  setoid_rewrite context_member_formula_correct. setoid_rewrite source_full_prv_formula_correct.
  reflexivity.
Qed.

Theorem source_descriptor_internal_common_context M T sb sc N:
  (forall f,context_member M sb sc N f ->source_descriptor_provable M T f) ->
  exists b c n,source_axiom_context M T b c n /\
    forall f,context_member M sb sc N f ->source_full_prv M b c n f.
Proof.
  intro HLocal.
  assert(HAll:forall k,source_internal_proof_context_at M T sb sc N k).
  { apply(definable_induction M(source_internal_proof_context_at M T sb sc N)
      (source_internal_proof_context_definable M T sb sc N)).
    - intros _. exists(zeroM M),(zeroM M),(zeroM M). split.
      + exact(source_axiom_context_empty M T).
      + intros f HF. exfalso. exact(context_empty M sb sc f HF).
    - intros k IH HKn.
      pose proof(proj1(coding_lt_succ_cancel M k N)HKn)as HK.
      assert(HKle:coding_lt M k(succM M N)).
      { apply(proj2(coding_lt_succ_cases M k N)). now left. }
      destruct(IH HKle)as(b&c&n&HOld&POld).
      destruct(beta_total M sb sc k)as(f&HF).
      destruct(HLocal f(ex_intro _ k(conj HK HF)))as(d&e&m&HNew&PNew).
      destruct(context_union_total M b c n d e m)as(u&v&l&HU).
      pose proof(source_axiom_context_union M T b c n d e m u v l HOld HNew HU)as HUnion.
      exists u,v,l. split;[exact HUnion|].
      intros a(i&HI&HA).
      destruct(proj1(coding_lt_succ_cases M i k)HI)as[HIk|E].
      + exact(source_full_prv_weaken_bounded M b c n u v l a(zeroM M)
          (POld a(ex_intro _ i(conj HIk HA)))
          (context_union_left M b c n d e m u v l HU)(proj1 HUnion)).
      + subst i. pose proof(beta_unique M sb sc k a f HA HF)as E. subst a.
        exact(source_full_prv_weaken_bounded M d e m u v l f(zeroM M)PNew
          (context_union_right M b c n d e m u v l HU)(proj1 HUnion)). }
  exact(HAll N(coding_lt_succ M N)).
Qed.

Theorem source_descriptor_internal_common_context_extending M T sb sc N ab ac an:
  source_axiom_context M T ab ac an ->
  (forall f,context_member M sb sc N f ->source_descriptor_provable M T f) ->
  exists b c n,source_axiom_context M T b c n /\context_included M ab ac an b c n /\
    forall f,context_member M sb sc N f ->source_full_prv M b c n f.
Proof.
  intros HA HP.
  destruct(source_descriptor_internal_common_context M T sb sc N HP)as(d&e&m&HD&P).
  destruct(context_union_total M ab ac an d e m)as(b&c&n&HU).
  pose proof(source_axiom_context_union M T ab ac an d e m b c n HA HD HU)as HC.
  exists b,c,n. split;[exact HC|]. split.
  - exact(context_union_left M ab ac an d e m b c n HU).
  - intros f HF. exact(source_full_prv_weaken_bounded M d e m b c n f(zeroM M)(P f HF)
      (context_union_right M ab ac an d e m b c n HU)(proj1 HC)).
Qed.

Print Assumptions source_internal_proof_context_definable.
Print Assumptions source_descriptor_internal_common_context.
Print Assumptions source_descriptor_internal_common_context_extending.

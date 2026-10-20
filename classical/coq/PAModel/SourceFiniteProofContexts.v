(** Combine a fixed finite family of actual numerical proofs. Formula
    codes and each proof's axiom context may be nonstandard. The finite
    list here describes a proof macro's finitely many premises. *)
From PAModel Require Import Model FiniteCoding NumericalTheories NumericalContexts
  ContextCombination SourceBounded SourceProofWeakening NumericalSourceFull
  SourceAxiomContexts SourceDescriptorProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_descriptor_finite_common_context M T (formulas:list(carrier M)) :
  (forall f,In f formulas ->source_descriptor_provable M T f) ->
  exists b c n,source_axiom_context M T b c n /\
    forall f,In f formulas ->source_full_prv M b c n f.
Proof.
  induction formulas as [|f formulas IH];intro HP.
  - exists (zeroM M),(zeroM M),(zeroM M). split;[apply source_axiom_context_empty|].
    intros h HH. destruct HH.
  - destruct (HP f (or_introl eq_refl)) as (b&c&n&HC&PF).
    destruct (IH ltac:(intros g HG;exact (HP g (or_intror HG)))) as (u&v&l&HU&PS).
    destruct (context_union_total M b c n u v l) as (ub&uc&un&HUnion).
    pose proof (source_axiom_context_union M T b c n u v l ub uc un HC HU HUnion) as HNew.
    exists ub,uc,un. split;[exact HNew|]. intros g [<-|HG].
    + exact (source_full_prv_weaken_bounded M b c n ub uc un f (zeroM M) PF
        (context_union_left M b c n u v l ub uc un HUnion) (proj1 HNew)).
    + exact (source_full_prv_weaken_bounded M u v l ub uc un g (zeroM M) (PS g HG)
        (context_union_right M b c n u v l ub uc un HUnion) (proj1 HNew)).
Qed.

Print Assumptions source_descriptor_finite_common_context.

(** Finite propositional programs for any arithmetic source-axiom descriptor. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceTraceBounds NumericalContexts NumericalSourceFull ContextCombination SourceAxiomContexts
  SourceDescriptorProvability SourceProofWeakening SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma source_descriptor_program_context M T A rho :
  (forall a,In a A ->forall f,code_relation M rho (source_prop_expression a) f ->source_descriptor_provable M T f) ->
  exists b c n,source_axiom_context M T b c n /\source_prop_hypotheses M rho A b c n.
Proof.
  intro H. induction A as [|a A IH].
  - exists (zeroM M),(zeroM M),(zeroM M). split;[apply source_axiom_context_empty|].
    intros p HP. contradiction.
  - destruct(code_relation_total M (source_prop_expression a) rho) as (f&HF).
    destruct(H a (or_introl eq_refl) f HF) as (b&c&n&HC&HP).
    destruct IH as (d&e&m&HD&HQ).
    { intros p HI g HG. exact(H p (or_intror HI) g HG). }
    destruct(context_union_total M b c n d e m) as (u&v&l&HU).
    pose proof(source_axiom_context_union M T b c n d e m u v l HC HD HU) as HCtx.
    exists u,v,l. split;[exact HCtx|]. intros p [<-|HI] g HG.
    + rewrite(code_relation_functional M _ rho g f HG HF).
      exact(source_full_prv_weaken_bounded M b c n u v l f (zeroM M) HP
        (context_union_left M b c n d e m u v l HU)(proj1 HCtx)).
    + exact(source_full_prv_weaken_bounded M d e m u v l g (zeroM M)(HQ p HI g HG)
        (context_union_right M b c n d e m u v l HU)(proj1 HCtx)).
Qed.

Theorem source_descriptor_prop_program M T A a :source_prop_program A a ->
  forall rho k f,(forall i,source_bounded M (rho i) k) ->
    (forall p,In p A ->forall g,code_relation M rho (source_prop_expression p) g ->source_descriptor_provable M T g) ->
    code_relation M rho (source_prop_expression a) f ->source_descriptor_provable M T f.
Proof.
  intros HP rho k f HB HH HF.
  destruct(source_descriptor_program_context M T A rho HH) as (b&c&n&HC&HH').
  exists b,c,n. split;[exact HC|].
  apply(source_prop_program_sound M A a HP rho k b c n f HB);[|exact HH'|exact HF].
  exact(context_bounded_monotone M b c n (zeroM M) k (proj1 HC)(coding_zero_lt_succ M k)).
Qed.

Print Assumptions source_descriptor_prop_program.

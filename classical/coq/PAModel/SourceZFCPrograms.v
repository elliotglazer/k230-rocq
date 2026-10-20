(** Fixed finite propositional programs can combine actual source ZFC
    proofs whose finite axiom contexts differ. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceTraceBounds NumericalContexts NumericalSourceFull ContextCombination
  SourceProofWeakening SourcePropositionalTemplates SourceZFCProvability SourceZFCBasicClosure.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma source_zfc_program_context M A rho :
  (forall a,In a A ->forall f,code_relation M rho (source_prop_expression a) f ->source_zfc_provable M f) ->
  exists b c n,source_zfc_context M b c n /\source_prop_hypotheses M rho A b c n.
Proof.
  intro H. induction A as [|a A IH].
  - exists (zeroM M),(zeroM M),(zeroM M). split.
    + intros f HF. exfalso. exact (context_empty M _ _ f HF).
    + intros p HP. contradiction.
  - destruct (code_relation_total M (source_prop_expression a) rho) as (f&HF).
    destruct (H a (or_introl eq_refl) f HF) as (b&c&n&HC&HP).
    destruct IH as (d&e&m&HD&HQ).
    { intros p HI g HG. exact (H p (or_intror HI) g HG). }
    destruct (context_union_total M b c n d e m) as (u&v&l&HU).
    pose proof (source_zfc_context_union M b c n d e m u v l HC HD HU) as HCtx.
    exists u,v,l. split;[exact HCtx|]. intros p [<-|HI] g HG.
    + rewrite (code_relation_functional M _ rho g f HG HF).
      exact (source_full_prv_weaken_bounded M b c n u v l f (zeroM M) HP
        (context_union_left M b c n d e m u v l HU) (source_zfc_context_closed M u v l HCtx)).
    + exact (source_full_prv_weaken_bounded M d e m u v l g (zeroM M) (HQ p HI g HG)
        (context_union_right M b c n d e m u v l HU) (source_zfc_context_closed M u v l HCtx)).
Qed.

Theorem source_zfc_prop_program M A a :source_prop_program A a ->
  forall rho k f,(forall i,source_bounded M (rho i) k) ->
    (forall p,In p A ->forall g,code_relation M rho (source_prop_expression p) g ->source_zfc_provable M g) ->
    code_relation M rho (source_prop_expression a) f ->source_zfc_provable M f.
Proof.
  intros HP rho k f HB HH HF.
  destruct (source_zfc_program_context M A rho HH) as (b&c&n&HC&HH').
  exists b,c,n. split;[exact HC|].
  apply (source_prop_program_sound M A a HP rho k b c n f HB);[|exact HH'|exact HF].
  exact (context_bounded_monotone M b c n (zeroM M) k
    (source_zfc_context_closed M b c n HC) (coding_zero_lt_succ M k)).
Qed.

Definition source_zfc_implies M a b :=forall f,sf_relation M SFImpl a b f ->source_zfc_provable M f.
Definition source_zfc_equivalent M a b :=source_zfc_implies M a b /\source_zfc_implies M b a.

Lemma source_zfc_implies_from_proof M a b f :sf_relation M SFImpl a b f ->
  source_zfc_provable M f ->source_zfc_implies M a b.
Proof.
  intros HF HP g HG. rewrite (sf_relation_functional M SFImpl a b g f HG HF). exact HP.
Qed.

Lemma source_zfc_equivalent_refl M a k :source_bounded M a k ->source_zfc_equivalent M a a.
Proof.
  intro HA. assert (H:source_zfc_implies M a a).
  { intros f HF. refine (source_zfc_prop_program M [] (SPTImpl (SPTSlot 0) (SPTSlot 0))
      _ (fun _=>a) k f _ _ _).
    - apply SPTII,SPTCtx. now left.
    - intros i. exact HA.
    - intros p HP. contradiction.
    - exact (source_prop_template_join M (fun _=>a) SFImpl (SPTSlot 0) (SPTSlot 0) a a f eq_refl eq_refl HF). }
  split;exact H.
Qed.

Print Assumptions source_zfc_prop_program.
Print Assumptions source_zfc_equivalent_refl.

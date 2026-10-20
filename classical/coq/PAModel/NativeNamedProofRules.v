(** A small set of actual source-proof consumers for the existing finite
    named templates. No new syntax compiler or theory axiom is introduced. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone NumericalContexts
  NumericalSourceFull SourceTraceBounds SourcePropositionalTemplates SourceSequents
  RawSourceImage RawSourceImageInversion NativeKBundle NativeNamedRegularity SourceNamedVacuity SourceNamedProofRules
  SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition native_source_proof M b c n env t :=forall out,
  native_named_evaluation M env t out ->source_full_prv M b c n out.

Theorem native_named_quantifier_view M env (universal:bool) name t result :
  native_named_evaluation M env (if universal then NNTAll name t else NNTEx name t) result ->
  exists x f,code_relation M env name x /\native_named_evaluation M env t f /\
    source_named_quantifier M universal x f result.
Proof.
  destruct universal;intros(x&f&rb&rc&body&HX&HF&HM&HR&HQ);exists x,f.
  all: split;[exact HX|].
  all: split;[exact HF|].
  all: exists rb,rc,body;auto.
Qed.

Theorem native_named_quantifier_join M env (universal:bool) name t x f result :
  code_relation M env name x ->native_named_evaluation M env t f ->
  source_named_quantifier M universal x f result ->
  native_named_evaluation M env (if universal then NNTAll name t else NNTEx name t) result.
Proof.
  intros HX HF (rb&rc&body&HM&HR&HQ). destruct universal;
    exists x,f,rb,rc,body;repeat first [assumption|split].
Qed.

Theorem native_named_evaluation_unique M env t :forall a b,
  native_named_evaluation M env t a ->native_named_evaluation M env t b ->a=b.
Proof.
  induction t as[i|eq x y|f IHF g IHG|f IHF g IHG|x f IH|x f IH];intros a b HA HB.
  - exact (raw_source_image_functional M (env i) a b HA HB).
  - destruct HA as(xv&yv&HX&HY&HO),HB as(xv'&yv'&HX'&HY'&HO').
    rewrite (code_relation_functional M x env xv' xv HX' HX) in HO'.
    rewrite (code_relation_functional M y env yv' yv HY' HY) in HO'.
    exact (sf_relation_functional M _ _ _ a b HO HO').
  - destruct HA as(u&v&HU&HV&HO),HB as(u'&v'&HU'&HV'&HO').
    rewrite (IHF u' u HU' HU),(IHG v' v HV' HV) in HO'.
    exact (sf_relation_functional M SFImpl u v a b HO HO').
  - destruct HA as(u&v&HU&HV&HO),HB as(u'&v'&HU'&HV'&HO').
    rewrite (IHF u' u HU' HU),(IHG v' v HV' HV) in HO'.
    exact (sf_relation_functional M SFAnd u v a b HO HO').
  - destruct (native_named_quantifier_view M env true x f a HA) as(name&body&HN&HF&HQ).
    destruct (native_named_quantifier_view M env true x f b HB) as(name'&body'&HN'&HF'&HQ').
    rewrite (code_relation_functional M x env name' name HN' HN),(IH body' body HF' HF) in HQ'.
    exact (source_named_quantifier_functional M true name body a b HQ HQ').
  - destruct (native_named_quantifier_view M env false x f a HA) as(name&body&HN&HF&HQ).
    destruct (native_named_quantifier_view M env false x f b HB) as(name'&body'&HN'&HF'&HQ').
    rewrite (code_relation_functional M x env name' name HN' HN),(IH body' body HF' HF) in HQ'.
    exact (source_named_quantifier_functional M false name body a b HQ HQ').
Qed.

Theorem native_source_ignore M b c n env f g :native_source_proof M b c n env g ->
  native_source_proof M b c n env (NNTImpl f g).
Proof.
  intros PG out (a&d&HA&HD&HI).
  destruct (native_named_evaluation_bounded M env f a HA) as(k&HK).
  exact (source_full_ignore_antecedent M b c n a d out k HK HI (PG d HD)).
Qed.

Theorem native_source_all_intro M b c n env x name f :
  code_relation M env name x ->source_named_context_vacuous M b c n x ->
  native_source_proof M b c n env f ->native_source_proof M b c n env (NNTAll name f).
Proof.
  intros HX HC PF out HO.
  destruct (native_named_quantifier_view M env true name f out HO) as(y&a&HY&HA&HQ).
  rewrite (code_relation_functional M name env y x HY HX) in HQ.
  exact (source_full_named_quantifier_all_intro M b c n x a out HC HQ (PF a HA)).
Qed.

Theorem native_source_exists_map M b c n env x name f g :
  code_relation M env name x ->source_named_context_vacuous M b c n x ->
  native_source_proof M b c n env (NNTImpl f g) ->
  native_source_proof M b c n env (NNTEx name f) ->native_source_proof M b c n env (NNTEx name g).
Proof.
  intros HX HC PI PEF out HO.
  destruct (native_named_quantifier_view M env false name g out HO) as(y&a&HY&HA&HQ).
  rewrite (code_relation_functional M name env y x HY HX) in HQ.
  destruct (native_named_evaluation_total M env f) as(d&HD).
  destruct (source_named_quantifier_total M false x d) as(exd&HExD).
  destruct (sf_relation_total M SFImpl d a) as(imp&HImp).
  exact (source_full_named_quantifier_ex_map M b c n x d a exd out imp HC HExD HQ HImp
    (PI imp (ex_intro _ d (ex_intro _ a (conj HD (conj HA HImp)))))
    (PEF exd (native_named_quantifier_join M env false name f x d exd HX HD HExD))).
Qed.

Lemma native_source_conjunct_replace_program :source_prop_program [SPTSlot 2]
  (SPTImpl (SPTAnd (SPTSlot 0)(SPTSlot 1))(SPTAnd (SPTSlot 0)(SPTSlot 2))).
Proof.
  apply SPTII,SPTCI.
  - apply (SPTCE1 _ (SPTSlot 0)(SPTSlot 1)),SPTCtx. now left.
  - apply SPTCtx. cbn;auto.
Qed.

Theorem native_source_conjunct_replace M b c n env f g h :
  native_source_proof M b c n env h ->
  native_source_proof M b c n env (NNTImpl (NNTAnd f g)(NNTAnd f h)).
Proof.
  intros PH out(left&right&(a&d&HA&HD&HL)&(a'&e&HA'&HE&HR)&HI).
  rewrite (native_named_evaluation_unique M env f a' a HA' HA) in HR.
  pose proof (PH e HE) as PE.
  destruct (source_full_prv_wellformed M b c n e PE) as(k&HB&HC).
  destruct (source_two_common_bounds M a d
    (native_named_evaluation_bounded M env f a HA)
    (native_named_evaluation_bounded M env g d HD)) as(l&HBA&HBD).
  set (bound:=addM M k l).
  assert (HBounds:forall i,source_bounded M (code_parameters a d e e i) bound).
  { intros [|[|[|i]]];cbn [code_parameters].
    - apply (source_bounded_monotone M a l bound HBA). unfold bound;rewrite add_comm;apply coding_le_add.
    - apply (source_bounded_monotone M d l bound HBD). unfold bound;rewrite add_comm;apply coding_le_add.
    - exact (source_bounded_monotone M e k bound HB (coding_le_add M k l)).
    - exact (source_bounded_monotone M e k bound HB (coding_le_add M k l)). }
  apply (source_prop_program_sound M _ _ native_source_conjunct_replace_program
    (code_parameters a d e e) bound b c n out HBounds
    (context_bounded_monotone M b c n k bound HC (coding_le_add M k l))).
  - intros p [<-|[]] v HV. change (v=e) in HV. now subst v.
  - exact (source_prop_template_join M (code_parameters a d e e) SFImpl
      (SPTAnd (SPTSlot 0)(SPTSlot 1))(SPTAnd (SPTSlot 0)(SPTSlot 2)) left right out
      (source_prop_template_join M _ SFAnd (SPTSlot 0)(SPTSlot 1) a d left eq_refl eq_refl HL)
      (source_prop_template_join M _ SFAnd (SPTSlot 0)(SPTSlot 2) a e right eq_refl eq_refl HR) HI).
Qed.

Print Assumptions native_source_all_intro.
Print Assumptions native_source_exists_map.
Print Assumptions native_source_conjunct_replace.

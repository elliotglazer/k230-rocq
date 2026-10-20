(** A finite certificate adapter, not an internal proof-length induction.
    Each certificate has a standard finite tree, but every raw formula code
    and every produced source proof may lie anywhere in the PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalContexts NumericalEnvironments SourceSequents NumericalSourceFull
  RawSourceImage RawSourceImageInversion RawSourcePropositional RawSourceClassical.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Inductive raw_prop_certificate (M:Model) : list (carrier M) -> carrier M -> Prop :=
| rpc_hyp Gamma f : In f Gamma -> raw_prop_certificate M Gamma f
| rpc_true Gamma : raw_prop_certificate M Gamma (zeroM M)
| rpc_intro Gamma a b h : implication_graph M a b h ->
    raw_prop_certificate M (a::Gamma) b -> raw_prop_certificate M Gamma h
| rpc_elim Gamma a b h : implication_graph M a b h ->
    raw_prop_certificate M Gamma h -> raw_prop_certificate M Gamma a ->
    raw_prop_certificate M Gamma b
| rpc_peirce Gamma a d x y f : implication_graph M a d x ->
    implication_graph M x a y -> implication_graph M y a f -> raw_prop_certificate M Gamma f.

Theorem raw_prop_certificate_source M Gamma f : raw_prop_certificate M Gamma f ->
  forall b c n bound,context_bounded M b c n bound ->
  (forall a,In a Gamma -> exists sa,raw_source_image M a sa /\ context_member M b c n sa) ->
  forall sf,raw_source_image M f sf -> source_full_prv M b c n sf.
Proof.
  intro H. induction H as [Gamma f HH|Gamma|Gamma a d h HI HP IH|Gamma a d h HI HP IHP HA IHA|
    Gamma a d x y f HX HY HF];intros b c n bound HC HM sf HS.
  - destruct (HM f HH) as (sa&HA&HCx).
    rewrite (raw_source_image_functional M f sa sf HA HS) in HCx.
    apply full_source_Ctx;[exact (raw_source_image_sequent_wf M b c n bound f sf HC HS)|exact HCx].
  - exact (source_full_truth M b c n sf (raw_source_image_sequent_wf M b c n bound _ sf HC HS)
      (raw_source_zero_inv M sf HS)).
  - destruct (raw_source_image_total M a) as [sa HSa].
    destruct (raw_source_image_total M d) as [sd HSd].
    destruct (environment_cons_total M b c n sa) as (eb&ec&en&HE).
    apply (raw_source_implication_intro M b c n bound a d h sa sd sf eb ec en HC HSa HSd HS HI HE).
    destruct (raw_source_context_extend_bounded M b c n bound a sa eb ec en HC HSa HE) as [kb HCB].
    apply (IH eb ec en kb HCB);[|exact HSd].
    intros r [<-|HR].
    + exists sa. split;[exact HSa|].
      apply (proj2 (context_member_cons M b c n sa eb ec en sa HE)). now left.
    + destruct (HM r HR) as (sr&HSr&HCr). exists sr. split;[exact HSr|].
      apply (proj2 (context_member_cons M b c n sa eb ec en sr HE)). now right.
  - destruct (raw_source_image_total M a) as [sa HSa].
    destruct (raw_source_image_total M h) as [sh HSh].
    exact (raw_source_implication_elim M b c n bound a d h sa sf sh HC HSa HS HSh HI
      (IHA b c n bound HC HM sa HSa) (IHP b c n bound HC HM sh HSh)).
  - exact (raw_source_peirce M b c n bound a d x y f sf HC HX HY HF HS).
Qed.

Corollary raw_prop_certificate_empty_source M f sf :
  raw_prop_certificate M [] f -> raw_source_image M f sf ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) sf.
Proof.
  intros HP HS. apply (raw_prop_certificate_source M [] f HP _ _ _ (zeroM M)).
  - apply context_bounded_empty.
  - intros a H. contradiction.
  - exact HS.
Qed.

Print Assumptions raw_prop_certificate_source.
Print Assumptions raw_prop_certificate_empty_source.

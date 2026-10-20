(** A finite constructor skeleton commutes with an actual source cutoff
    shift. Arbitrary internal holes are shifted at their true binder depth. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent
  QuotationRules QuotationSchemaSkeleton SourceFiniteCutoffShift SourceFiniteContexts SetSchemaConstructors SourceTraceMatrixAlignment
  NumericalSubstitutionMaps NumericalSubstitution SourcePropositionalRebase SourceWFSeparationConstructor.
From Stdlib Require Import Lia.
From Undecidability.FOL Require Import Syntax.Facts.
Unset Implicit Arguments.

Lemma source_shift_sigma_fixed_index depth i :i<depth ->sf_index (source_shift_sigma depth i)=i.
Proof.
  induction depth as [|depth IH] in i |- *;intros H;[lia|].
  destruct i as [|i];[reflexivity|]. change (sf_index (up (source_shift_sigma depth) (S i))=S i).
  rewrite source_up_substitution_index.
  rewrite IH;[reflexivity|lia].
Qed.

Theorem source_cutoff_shift_maps_equivalent M depth b c n d e m :
  source_cutoff_shift_map M depth b c n ->source_cutoff_shift_map M depth d e m ->
  substitution_equivalent M b c n d e m (code_numeral M (S depth)).
Proof.
  revert b c n d e m. induction depth as [|depth IH];intros b c n d e m HB HD.
  - destruct HB as [-> [-> ->]],HD as [-> [-> ->]]. apply substitution_equivalent_refl.
  - destruct HB as (u&v&l&HU&HL),HD as (p&q&k&HP&HK).
    exact (substitution_lift_extensional M u v l p q k (code_numeral M (S depth))
      b c n d e m (IH u v l p q k HU HP) HL HK).
Qed.

Fixpoint skeleton_cutoff_holes M depth s sources outputs :Prop :=
  match s with
  | SkeletonHole i=>source_cutoff_shift M depth (sources i)(outputs i)
  | SkeletonFalse=>True
  | SkeletonAtom _ i j=>i<depth /\ j<depth
  | SkeletonBinary _ a b=>skeleton_cutoff_holes M depth a sources outputs /\
      skeleton_cutoff_holes M depth b sources outputs
  | SkeletonQuantifier _ a=>skeleton_cutoff_holes M (S depth) a sources outputs
  end.

Theorem skeleton_cutoff_substitution M s :forall depth sources outputs b c n f g,
  source_cutoff_shift_map M depth b c n ->skeleton_cutoff_holes M depth s sources outputs ->
  code_relation M sources (skeleton_code s) f ->code_relation M outputs (skeleton_code s) g ->
  numerical_substitution M f b c n (code_numeral M (S depth)) g.
Proof.
  induction s as [i| |eq i j|op a IHa d IHd|univ a IH];intros depth sources outputs b c n f g HM HH HF HG.
  - change (f=sources i) in HF. change (g=outputs i) in HG. subst f g.
    destruct HH as (u&v&m&HU&HS).
    exact (proj1 (numerical_substitution_extensional M (sources i) u v m b c n
      (code_numeral M (S depth))(outputs i)
      (source_cutoff_shift_maps_equivalent M depth u v m b c n HU HM)) HS).
  - change (f=zeroM M) in HF. change (g=zeroM M) in HG. subst f g.
    apply (proj2 (numerical_substitution_invalid M (zeroM M) b c n (code_numeral M (S depth))
      (zeroM M)(or_introl eq_refl))). reflexivity.
  - destruct HH as [HI HJ].
    assert (HA:sf_relation M (quotation_source_atom eq)(code_numeral M i)(code_numeral M j) f).
    { exact (proj1 (skeleton_source_relation M sources (quotation_source_atom eq)(CEconst i)(CEconst j) (code_numeral M i)(code_numeral M j) f eq_refl eq_refl) HF). }
    assert (HB:sf_relation M (quotation_source_atom eq)(code_numeral M i)(code_numeral M j) g).
    { exact (proj1 (skeleton_source_relation M outputs (quotation_source_atom eq)(CEconst i)(CEconst j) (code_numeral M i)(code_numeral M j) g eq_refl eq_refl) HG). }
    assert (LI:substitution_lookup M b c n (code_numeral M (S depth))(code_numeral M i)(code_numeral M i)).
    { pose proof (source_cutoff_shift_map_fixed_lookup M depth b c n HM i) as H.
      rewrite (source_shift_sigma_fixed_index depth i HI) in H. exact H. }
    assert (LJ:substitution_lookup M b c n (code_numeral M (S depth))(code_numeral M j)(code_numeral M j)).
    { pose proof (source_cutoff_shift_map_fixed_lookup M depth b c n HM j) as H.
      rewrite (source_shift_sigma_fixed_index depth j HJ) in H. exact H. }
    destruct eq.
    + apply (proj2 (numerical_substitution_equal M _ _ _ b c n _ g HA)).
      exists (code_numeral M i),(code_numeral M j). auto.
    + apply (proj2 (numerical_substitution_member M _ _ _ b c n _ g HA)).
      exists (code_numeral M i),(code_numeral M j). auto.
  - destruct HH as [HA HD].
    destruct (schema_expression_split M sources (skeleton_head op) _ _ f HF) as (x&y&HX&HY&HXY).
    destruct (schema_expression_split M outputs (skeleton_head op) _ _ g HG) as (x'&y'&HX'&HY'&HXY').
    apply (proj2 (numerical_substitution_binary M (skeleton_head op) x y f b c n
      (code_numeral M (S depth)) g ltac:(destruct op;unfold sf_binary,skeleton_head;auto) HXY)).
    exists x',y'. split;[exact (IHa depth sources outputs b c n x x' HM HA HX HX')|].
    split;[exact (IHd depth sources outputs b c n y y' HM HD HY HY')|exact HXY'].
  - destruct (schema_expression_quantifier_split M sources (quotation_source_quantifier univ) _ f HF)
      as (x&HX&HAll).
    destruct (schema_expression_quantifier_split M outputs (quotation_source_quantifier univ) _ g HG)
      as (x'&HX'&HAll').
    destruct (substitution_lift_total M b c n (code_numeral M (S depth))) as (u&v&m&HL).
    apply (proj2 (numerical_substitution_quantifier M univ x f b c n (code_numeral M (S depth)) g HAll)).
    exists u,v,m,x'. split;[exact HL|]. split;[|exact HAll'].
    apply (IH (S depth) sources outputs u v m x x');try assumption.
    exists b,c,n. auto.
Qed.

Theorem skeleton_source_cutoff_shift M s depth sources outputs f g :
  skeleton_cutoff_holes M depth s sources outputs ->
  code_relation M sources (skeleton_code s) f ->code_relation M outputs (skeleton_code s) g ->
  source_cutoff_shift M depth f g.
Proof.
  intros HH HF HG. destruct (source_cutoff_shift_map_total M depth) as (b&c&n&HM).
  exists b,c,n. split;[exact HM|]. exact (skeleton_cutoff_substitution M s depth sources outputs b c n f g HM HH HF HG).
Qed.

Print Assumptions source_cutoff_shift_maps_equivalent.
Print Assumptions skeleton_source_cutoff_shift.

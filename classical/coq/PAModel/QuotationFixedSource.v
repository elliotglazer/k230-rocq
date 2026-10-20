(** Arbitrary-model certification for a fixed external finite source formula.
    Arithmetic parameters may be nonstandard. The source graph is constrained
    by that particular finite formula. The structural induction is on it;
    no induction over arbitrary internal formulas is asserted here. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  ProofTemplates SetFormulaCodes ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  NumericalEnvironments QuotationPayloads QuotationRules NumericalQuotation QuotationSource.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma sf_expression_constructor_graph M rho h A B a b f :
  code_relation M rho A a -> code_relation M rho B b ->
  (code_relation M rho (E_sf h A B) f <-> sf_relation M h a b f).
Proof.
  intros HA HB.
  replace (E_sf h A B) with
    (code_subst (sf_env A B) (E_sf h (CEvar 0) (CEvar 1)))
    by (destruct h; reflexivity).
  unfold sf_relation. apply code_subst_graph.
  intros [|i]; cbn [sf_env]; assumption.
Qed.

Lemma quotation_atom_substitution_graph M rho equality X Y D K x y d k v :
  code_relation M rho X x -> code_relation M rho Y y ->
  code_relation M rho D d -> code_relation M rho K k ->
  (code_relation M rho
    (code_subst (quotation_atom_parameters X Y D K (CEconst 0))
      (quotation_atom_expression equality)) v <->
   quotation_atom M equality x y d k v).
Proof.
  intros HX HY HD HK. unfold quotation_atom. apply code_subst_graph.
  intros [|[|[|[|i]]]]; cbn [quotation_atom_parameters scons]; auto; reflexivity.
Qed.

Lemma quotation_binary_substitution_graph M rho h X Y x y v :
  code_relation M rho X x -> code_relation M rho Y y ->
  (code_relation M rho
    (code_subst (X .: Y .: fun _ => CEconst 0) (quotation_binary_expression h)) v <->
   quotation_binary M h x y v).
Proof.
  intros HX HY. unfold quotation_binary. apply code_subst_graph.
  intros [|[|i]]; cbn [scons]; auto; reflexivity.
Qed.

Lemma quotation_quantifier_substitution_graph M rho universal K D X k d x v :
  code_relation M rho K k -> code_relation M rho D d -> code_relation M rho X x ->
  (code_relation M rho
    (code_subst (K .: D .: X .: fun _ => CEconst 0)
      (quotation_quantifier_expression universal)) v <->
   quotation_quantifier M universal k d x v).
Proof.
  intros HK HD HX. unfold quotation_quantifier. apply code_subst_graph.
  intros [|[|[|i]]]; cbn [scons]; auto; reflexivity.
Qed.

Lemma code_graph_fresh_successor M rho fresh k :
  code_relation M rho fresh k ->
  code_relation M rho (CEadd fresh (CEconst 1)) (succM M k).
Proof.
  intro H. exists k,(code_numeral M 1). split; [exact H|].
  split; [reflexivity|]. apply succ_as_add.
Qed.

Theorem fixed_source_quotation {ff} M rho
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall env fresh domain eta k d f v eb ec en,
  (forall i, code_relation M rho (env i) (eta i)) ->
  (forall i, environment_lookup M eb ec en (code_numeral M i) (eta i)) ->
  code_relation M rho fresh k -> code_relation M rho domain d ->
  code_relation M rho (sf_expression phi) f ->
  code_relation M rho (quotation_expression env fresh domain phi) v ->
  numerical_quotation M f eb ec en k d v.
Proof.
  induction phi; intros env fresh domain eta k d f v eb ec en Henv Hlookup Hk Hd Hf Hv.
  - change (f = zeroM M) in Hf. change (v = code_numeral M 1) in Hv.
    subst f v. apply numerical_quotation_leaf. left. split; [now left|reflexivity].
  - destruct P.
    + apply numerical_quotation_leaf. right; left.
      exists (code_numeral M (sf_index (Vector.hd t))),
        (code_numeral M (sf_index (Vector.hd (Vector.tl t)))),
        (eta (sf_index (Vector.hd t))),(eta (sf_index (Vector.hd (Vector.tl t)))).
      split.
      * apply (proj1 (sf_expression_constructor_graph M rho SFMember
          (CEconst (sf_index (Vector.hd t))) (CEconst (sf_index (Vector.hd (Vector.tl t)))) _ _ f
          eq_refl eq_refl)). exact Hf.
      * split; [apply Hlookup|]. split; [apply Hlookup|].
        apply (proj1 (quotation_atom_substitution_graph M rho false _ _ _ _ _ _ _ _ v
          (Henv _) (Henv _) Hd Hk)). exact Hv.
    + apply numerical_quotation_leaf. right; right.
      exists (code_numeral M (sf_index (Vector.hd t))),
        (code_numeral M (sf_index (Vector.hd (Vector.tl t)))),
        (eta (sf_index (Vector.hd t))),(eta (sf_index (Vector.hd (Vector.tl t)))).
      split.
      * apply (proj1 (sf_expression_constructor_graph M rho SFEqual
          (CEconst (sf_index (Vector.hd t))) (CEconst (sf_index (Vector.hd (Vector.tl t)))) _ _ f
          eq_refl eq_refl)). exact Hf.
      * split; [apply Hlookup|]. split; [apply Hlookup|].
        apply (proj1 (quotation_atom_substitution_graph M rho true _ _ _ _ _ _ _ _ v
          (Henv _) (Henv _) Hd Hk)). exact Hv.
  - destruct (code_relation_total M (sf_expression phi1) rho) as [a Ha].
    destruct (code_relation_total M (sf_expression phi2) rho) as [b' Hb].
    destruct (code_relation_total M (quotation_expression env fresh domain phi1) rho) as [x Hx].
    destruct (code_relation_total M (quotation_expression env fresh domain phi2) rho) as [y Hy].
    pose proof (IHphi1 env fresh domain eta k d a x eb ec en Henv Hlookup Hk Hd Ha Hx) as Ix.
    pose proof (IHphi2 env fresh domain eta k d b' y eb ec en Henv Hlookup Hk Hd Hb Hy) as Iy.
    destruct b0.
    + eapply (numerical_quotation_binary M SFAnd a b' f eb ec en k d x y v).
      * unfold SetCodeDescent.sf_binary. now left.
      * exact (proj1 (sf_expression_constructor_graph M rho SFAnd _ _ a b' f Ha Hb) Hf).
      * exact Ix.
      * exact Iy.
      * exact (proj1 (quotation_binary_substitution_graph M rho SFAnd _ _ x y v Hx Hy) Hv).
    + eapply (numerical_quotation_binary M SFOr a b' f eb ec en k d x y v).
      * unfold SetCodeDescent.sf_binary. right; now left.
      * exact (proj1 (sf_expression_constructor_graph M rho SFOr _ _ a b' f Ha Hb) Hf).
      * exact Ix.
      * exact Iy.
      * exact (proj1 (quotation_binary_substitution_graph M rho SFOr _ _ x y v Hx Hy) Hv).
    + eapply (numerical_quotation_binary M SFImpl a b' f eb ec en k d x y v).
      * unfold SetCodeDescent.sf_binary. right; now right.
      * exact (proj1 (sf_expression_constructor_graph M rho SFImpl _ _ a b' f Ha Hb) Hf).
      * exact Ix.
      * exact Iy.
      * exact (proj1 (quotation_binary_substitution_graph M rho SFImpl _ _ x y v Hx Hy) Hv).
  - destruct (code_relation_total M (sf_expression phi) rho) as [a Ha].
    destruct (code_relation_total M
      (quotation_expression (fresh .: env) (CEadd fresh (CEconst 1)) domain phi) rho) as [w Hw].
    destruct (environment_cons_total M eb ec en k) as [eb' [ec' [en' Hcons]]].
    assert (Henv' : forall i, code_relation M rho ((fresh .: env) i) ((k .: eta) i)).
    { intros [|i]; cbn; auto. }
    assert (Hlookup' : forall i, environment_lookup M eb' ec' en'
      (code_numeral M i) ((k .: eta) i)).
    { intros [|i]; cbn [code_numeral scons].
      - apply (proj2 (environment_cons_head M eb ec en k eb' ec' en' k Hcons)). reflexivity.
      - apply (proj2 (environment_cons_tail M eb ec en k eb' ec' en'
          (code_numeral M i) (eta i) Hcons)). apply Hlookup. }
    pose proof (IHphi (fresh .: env) (CEadd fresh (CEconst 1)) domain
      (k .: eta) (succM M k) d a w eb' ec' en' Henv' Hlookup'
      (code_graph_fresh_successor M rho fresh k Hk) Hd Ha Hw) as Iw.
    destruct q.
    + eapply (numerical_quotation_unary M true a f eb ec en k d eb' ec' en' w v).
      * exact (proj1 (sf_expression_constructor_graph M rho SFAll _ (CEconst 0) a (zeroM M) f Ha eq_refl) Hf).
      * exact Hcons.
      * exact Iw.
      * exact (proj1 (quotation_quantifier_substitution_graph M rho true _ _ _ k d w v Hk Hd Hw) Hv).
    + eapply (numerical_quotation_unary M false a f eb ec en k d eb' ec' en' w v).
      * exact (proj1 (sf_expression_constructor_graph M rho SFEx _ (CEconst 0) a (zeroM M) f Ha eq_refl) Hf).
      * exact Hcons.
      * exact Iw.
      * exact (proj1 (quotation_quantifier_substitution_graph M rho false _ _ _ k d w v Hk Hd Hw) Hv).
Qed.

Corollary fixed_source_quotation_exists {ff} M rho
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff)
    env fresh domain eta k d f eb ec en :
  (forall i, code_relation M rho (env i) (eta i)) ->
  (forall i, environment_lookup M eb ec en (code_numeral M i) (eta i)) ->
  code_relation M rho fresh k -> code_relation M rho domain d ->
  code_relation M rho (sf_expression phi) f ->
  exists v, code_relation M rho (quotation_expression env fresh domain phi) v /\
    numerical_quotation M f eb ec en k d v.
Proof.
  intros Henv Hlookup Hk Hd Hf.
  destruct (code_relation_total M (quotation_expression env fresh domain phi) rho) as [v Hv].
  exists v. split; [exact Hv|].
  exact (fixed_source_quotation M rho phi env fresh domain eta k d f v eb ec en
    Henv Hlookup Hk Hd Hf Hv).
Qed.

Corollary fixed_ZFC_axiom_quotation M rho tag env fresh domain eta k d f v eb ec en :
  (forall i, code_relation M rho (env i) (eta i)) ->
  (forall i, environment_lookup M eb ec en (code_numeral M i) (eta i)) ->
  code_relation M rho fresh k -> code_relation M rho domain d ->
  code_relation M rho (zfc_fixed_source_expression tag) f ->
  code_relation M rho (quotation_expression env fresh domain (zfc_fixed_source tag)) v ->
  numerical_quotation M f eb ec en k d v.
Proof. apply fixed_source_quotation. Qed.

Print Assumptions fixed_source_quotation.
Print Assumptions fixed_source_quotation_exists.
Print Assumptions fixed_ZFC_axiom_quotation.

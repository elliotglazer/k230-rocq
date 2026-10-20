(** Expanding a fixed source constructor around arbitrary internal formula
    codes. Holes are quoted in their actual binder environments; their
    contents need not be standard formulas. This is a syntactic bridge. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  ProofTemplates SetFormulaCodes SetCodeDescent SetSchemaConstructors NumericalQuotation
  QuotationRules QuotationPayloads QuotationFunctionality NumericalEnvironments.
Unset Implicit Arguments.

Inductive skeleton_binary := SkeletonAnd | SkeletonOr | SkeletonImpl.
Definition skeleton_head op :=
  match op with SkeletonAnd=>SFAnd|SkeletonOr=>SFOr|SkeletonImpl=>SFImpl end.
Inductive source_skeleton :=
| SkeletonHole : nat -> source_skeleton
| SkeletonFalse : source_skeleton
| SkeletonAtom : bool -> nat -> nat -> source_skeleton
| SkeletonBinary : skeleton_binary -> source_skeleton -> source_skeleton -> source_skeleton
| SkeletonQuantifier : bool -> source_skeleton -> source_skeleton.

Fixpoint skeleton_code s : code_expr :=
  match s with
  | SkeletonHole i => CEvar i
  | SkeletonFalse => CEconst 0
  | SkeletonAtom equality i j =>
      E_sf (quotation_source_atom equality) (CEconst i) (CEconst j)
  | SkeletonBinary op a b => E_sf (skeleton_head op) (skeleton_code a) (skeleton_code b)
  | SkeletonQuantifier universal a =>
      E_sf (quotation_source_quantifier universal) (skeleton_code a) (CEconst 0)
  end.

Fixpoint skeleton_quotation M s sources b c n k t v : Prop :=
  match s with
  | SkeletonHole i => numerical_quotation M (sources i) b c n k t v
  | SkeletonFalse => v=code_numeral M 1
  | SkeletonAtom equality i j => exists x y,
      environment_lookup M b c n (code_numeral M i) x /\
      environment_lookup M b c n (code_numeral M j) y /\ quotation_atom M equality x y t k v
  | SkeletonBinary op a d => exists x y,
      skeleton_quotation M a sources b c n k t x /\
      skeleton_quotation M d sources b c n k t y /\ quotation_binary M (skeleton_head op) x y v
  | SkeletonQuantifier universal a => exists db dc dn x,
      environment_cons M b c n k db dc dn /\
      skeleton_quotation M a sources db dc dn (succM M k) t x /\
      quotation_quantifier M universal k t x v
  end.

Lemma skeleton_source_relation M sources h a b x y f :
  code_relation M sources a x -> code_relation M sources b y ->
  (code_relation M sources (E_sf h a b) f <-> sf_relation M h x y f).
Proof.
  intros HA HB.
  assert (E : E_sf h a b = code_subst (sf_env a b) (E_sf h (CEvar 0) (CEvar 1))).
  { destruct h;reflexivity. }
  rewrite E. unfold sf_relation.
  apply code_subst_graph. intros [|i];[exact HA|exact HB].
Qed.

Theorem skeleton_quotation_correct M s :
  forall sources f, code_relation M sources (skeleton_code s) f ->
  forall b c n k t v,
    skeleton_quotation M s sources b c n k t v <-> numerical_quotation M f b c n k t v.
Proof.
  induction s as [i| |equality i j|op a IHa d IHd|universal a IH];
    intros sources f HF b c n k t v.
  - change (f=sources i) in HF. now subst f.
  - change (f=zeroM M) in HF. subst f. cbn [skeleton_quotation]. split.
    + intros ->. apply numerical_quotation_leaf. left. split;[now left|reflexivity].
    + intro HQ. apply (numerical_quotation_invalid M (zeroM M) b c n k t v);[now left|exact HQ].
  - assert (HS : sf_relation M (quotation_source_atom equality)
        (code_numeral M i) (code_numeral M j) f).
    { apply (proj1 (skeleton_source_relation M sources (quotation_source_atom equality)
        (CEconst i) (CEconst j) (code_numeral M i) (code_numeral M j) f eq_refl eq_refl)). exact HF. }
    cbn [skeleton_quotation]. split.
    + intros [x [y [HX [HY HQ]]]]. apply numerical_quotation_leaf.
      destruct equality;[right;right|right;left];
        exists (code_numeral M i),(code_numeral M j),x,y;repeat split;assumption.
    + intro HQ. exact (numerical_quotation_atom_inv M equality
        (code_numeral M i) (code_numeral M j) f b c n k t v HS HQ).
  - destruct (code_relation_total M (skeleton_code a) sources) as [x HX].
    destruct (code_relation_total M (skeleton_code d) sources) as [y HY].
    assert (HS : sf_relation M (skeleton_head op) x y f).
    { exact (proj1 (skeleton_source_relation M sources (skeleton_head op)
        (skeleton_code a) (skeleton_code d) x y f HX HY) HF). }
    assert (HB : sf_binary (skeleton_head op)).
    { destruct op;unfold skeleton_head,sf_binary;auto. }
    cbn [skeleton_quotation]. split.
    + intros [u [w [HU [HW HOut]]]].
      apply (numerical_quotation_binary M (skeleton_head op) x y f b c n k t u w v HB HS).
      * exact (proj1 (IHa sources x HX b c n k t u) HU).
      * exact (proj1 (IHd sources y HY b c n k t w) HW).
      * exact HOut.
    + intro HQ. destruct (numerical_quotation_binary_inv M (skeleton_head op) x y f
        b c n k t v HB HS HQ) as [u [w [HU [HW HOut]]]].
      exists u,w. split;[exact (proj2 (IHa sources x HX b c n k t u) HU)|].
      split;[exact (proj2 (IHd sources y HY b c n k t w) HW)|exact HOut].
  - destruct (code_relation_total M (skeleton_code a) sources) as [x HX].
    assert (HS : sf_relation M (quotation_source_quantifier universal) x (zeroM M) f).
    { exact (proj1 (skeleton_source_relation M sources (quotation_source_quantifier universal)
        (skeleton_code a) (CEconst 0) x (zeroM M) f HX eq_refl) HF). }
    cbn [skeleton_quotation]. split.
    + intros [db [dc [dn [u [HEnv [HU HOut]]]]]].
      apply (numerical_quotation_unary M universal x f b c n k t db dc dn u v HS HEnv).
      * exact (proj1 (IH sources x HX db dc dn (succM M k) t u) HU).
      * exact HOut.
    + intro HQ. destruct (numerical_quotation_unary_inv M universal x f b c n k t v HS HQ)
        as [db [dc [dn [u [HEnv [HU HOut]]]]]].
      exists db,dc,dn,u. split;[exact HEnv|].
      split;[exact (proj2 (IH sources x HX db dc dn (succM M k) t u) HU)|exact HOut].
Qed.

Definition skeleton_and := SkeletonBinary SkeletonAnd.
Definition skeleton_impl := SkeletonBinary SkeletonImpl.
Definition skeleton_iff a b := skeleton_and (skeleton_impl a b) (skeleton_impl b a).
Definition separation_skeleton := SkeletonQuantifier true (SkeletonQuantifier false
  (SkeletonQuantifier true (skeleton_iff (SkeletonAtom false 0 1)
    (skeleton_and (SkeletonAtom false 0 2) (SkeletonHole 0))))).
Definition functionality_skeleton := SkeletonQuantifier true (SkeletonQuantifier true
  (SkeletonQuantifier true (skeleton_impl (SkeletonHole 0)
    (skeleton_impl (SkeletonHole 1) (SkeletonAtom true 1 0))))).
Definition replacement_skeleton := skeleton_impl functionality_skeleton
  (SkeletonQuantifier true (SkeletonQuantifier false (SkeletonQuantifier true
    (skeleton_iff (SkeletonAtom false 0 1)
      (SkeletonQuantifier false (skeleton_and (SkeletonAtom false 0 3) (SkeletonHole 2))))))).

Lemma separation_skeleton_code : skeleton_code separation_skeleton = E_sf_separation (CEvar 0).
Proof. reflexivity. Qed.
Lemma replacement_skeleton_code : skeleton_code replacement_skeleton =
  E_sf_replacement (CEvar 0) (CEvar 1) (CEvar 2).
Proof. reflexivity. Qed.

Theorem separation_quotation_skeleton M body f b c n k t v :
  sf_separation_constructor M body f ->
  (skeleton_quotation M separation_skeleton (fun _=>body) b c n k t v <->
    numerical_quotation M f b c n k t v).
Proof. intro HF. apply skeleton_quotation_correct. exact HF. Qed.
Theorem replacement_quotation_skeleton M a d e f b c n k t v :
  sf_replacement_constructor M a d e f ->
  (skeleton_quotation M replacement_skeleton (schema_env3 a d e) b c n k t v <->
    numerical_quotation M f b c n k t v).
Proof. intro HF. apply skeleton_quotation_correct. exact HF. Qed.

Print Assumptions skeleton_quotation_correct.
Print Assumptions separation_quotation_skeleton.
Print Assumptions replacement_quotation_skeleton.

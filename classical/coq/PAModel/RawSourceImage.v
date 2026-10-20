(** Numerical decoding of the machine's four-tag named syntax into full
    de Bruijn source syntax. Raw zero is interpreted as source truth;
    consequently implication preservation is literal only at nonzero raw
    implication codes. This graph makes no source-provability assertion. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  CodeExpressions CodeDescent CodeTags NumericalProofs NumericalTraces SentenceBounds
  SetFormulaCodes NumericalRenaming RawBinderRenaming.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque holds sf_formula tagged_pair_formula pair_formula universal_formula
  raw_binder_renaming_formula numerical_renaming_formula trace_derives_formula.

Definition raw_source_base M f s :=
  (f=zeroM M /\ sf_relation M SFImpl (zeroM M) (zeroM M) s) \/
  (exists a b,membership_graph M a b f /\ sf_relation M SFMember a b s) \/
  (exists a b,equality_graph M a b f /\ sf_relation M SFEqual a b s).
Definition raw_source_base_formula (f s:term) : form :=
  ((f == zero) ∧ sf_formula SFImpl zero zero s) ∨
  ((∃∃ (tagged_pair_formula 1 $1 $0 (code_lift2 f) ∧
      sf_formula SFMember $1 $0 (code_lift2 s))) ∨
   (∃∃ (tagged_pair_formula 3 $1 $0 (code_lift2 f) ∧
      sf_formula SFEqual $1 $0 (code_lift2 s)))).

Lemma raw_source_base_formula_correct M rho f s :
  holds M rho (raw_source_base_formula f s) <->
    raw_source_base M (evalM M rho f) (evalM M rho s).
Proof.
  unfold raw_source_base_formula,raw_source_base.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite sf_formula_correct.
  setoid_rewrite tagged_pair_formula_correct. setoid_rewrite code_eval_lift2.
  reflexivity.
Qed.

Definition raw_source_unary M row previous :=
  exists f s x g u b c v,
    pair_graph M f s row /\ pair_graph M g u previous /\ universal_graph M x g f /\
    raw_binder_renaming M x b c /\
    numerical_renaming M u b c (succM M x) (succM M (zeroM M)) v /\
    sf_relation M SFAll v (zeroM M) s.
Definition raw_source_unary_formula : form :=
  ∃∃∃∃∃∃∃∃ (pair_formula $7 $6 $8 ∧ (pair_formula $4 $3 $9 ∧
    (universal_formula $5 $4 $7 ∧ (raw_binder_renaming_formula $5 $2 $1 ∧
    (numerical_renaming_formula $3 $2 $1 (σ $5) (σ zero) $0 ∧ sf_formula SFAll $0 zero $6))))).

Lemma raw_source_unary_formula_correct M rho :
  holds M rho raw_source_unary_formula <-> raw_source_unary M (rho 0) (rho 1).
Proof.
  unfold raw_source_unary_formula,raw_source_unary.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite pair_formula_correct. setoid_rewrite universal_formula_correct.
  setoid_rewrite raw_binder_renaming_formula_correct. setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite sf_formula_correct. reflexivity.
Qed.

Definition raw_source_binary M row left right :=
  exists f s a b u v,
    pair_graph M f s row /\ pair_graph M a u left /\ pair_graph M b v right /\
    f<>zeroM M /\ implication_graph M a b f /\ sf_relation M SFImpl u v s.
Definition raw_source_binary_formula : form :=
  ∃∃∃∃∃∃ (pair_formula $5 $4 $6 ∧ (pair_formula $3 $1 $7 ∧ (pair_formula $2 $0 $8 ∧
    (($5 == zero → ⊥) ∧ (implication_formula $3 $2 $5 ∧ sf_formula SFImpl $1 $0 $4))))).

Lemma raw_source_binary_formula_correct M rho :
  holds M rho raw_source_binary_formula <-> raw_source_binary M (rho 0) (rho 1) (rho 2).
Proof.
  unfold raw_source_binary_formula,raw_source_binary.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite pair_formula_correct. setoid_rewrite implication_formula_correct.
  setoid_rewrite sf_formula_correct. reflexivity.
Qed.

Definition raw_source_row_base_formula : form :=
  ∃∃ (pair_formula $1 $0 $2 ∧ raw_source_base_formula $1 $0).
Definition raw_source_rules : NumericalRules.
Proof.
  refine {|rule_base_formula:=raw_source_row_base_formula;
    rule_unary_formula:=raw_source_unary_formula;rule_binary_formula:=raw_source_binary_formula|};
    apply formula_boundb_sound;vm_compute;reflexivity.
Defined.

Lemma raw_source_trace_base M row :
  trace_base M raw_source_rules row <-> exists f s,pair_graph M f s row /\ raw_source_base M f s.
Proof.
  unfold trace_base. change (holds M (row .: fun _=>zeroM M) raw_source_row_base_formula <-> exists f s,pair_graph M f s row /\ raw_source_base M f s).
  unfold raw_source_row_base_formula. repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite pair_formula_correct. setoid_rewrite raw_source_base_formula_correct. reflexivity.
Qed.
Lemma raw_source_trace_unary M row previous :
  trace_unary M raw_source_rules row previous <-> raw_source_unary M row previous.
Proof. apply raw_source_unary_formula_correct. Qed.
Lemma raw_source_trace_binary M row left right :
  trace_binary M raw_source_rules row left right <-> raw_source_binary M row left right.
Proof. apply raw_source_binary_formula_correct. Qed.

Definition raw_source_image M f s := exists row,pair_graph M f s row /\ trace_derives M raw_source_rules row.
Definition raw_source_image_formula (f s:term) : form :=
  ∃ (pair_formula f`[↑] s`[↑] $0 ∧ trace_derives_formula raw_source_rules $0).

Lemma raw_source_image_formula_correct M rho f s :
  holds M rho (raw_source_image_formula f s) <-> raw_source_image M (evalM M rho f) (evalM M rho s).
Proof.
  unfold raw_source_image_formula,raw_source_image. setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite pair_formula_correct. setoid_rewrite trace_derives_formula_correct.
  unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.

Lemma raw_source_image_exists_definable M : Definable1 M (fun f=>exists s,raw_source_image M f s).
Proof.
  exists (∃ raw_source_image_formula $1 $0),(fun _=>zeroM M).
  intro f. rewrite holds_ex. setoid_rewrite raw_source_image_formula_correct. reflexivity.
Qed.

Theorem raw_source_image_base M f s : raw_source_base M f s -> raw_source_image M f s.
Proof.
  intro H. destruct (pair_total M f s) as [row Hrow]. exists row. split;[exact Hrow|].
  apply trace_derives_base,raw_source_trace_base. exists f,s. auto.
Qed.

(** The nonzero premise is essential: raw wim(0,0)=0, while raw zero
    is mapped to source truth. The later proof transfer must handle that
    zero collision by a propositional derivation, not this constructor rule. *)
Theorem raw_source_image_implication M a b f u v s :
  f<>zeroM M -> implication_graph M a b f -> raw_source_image M a u -> raw_source_image M b v ->
  sf_relation M SFImpl u v s -> raw_source_image M f s.
Proof.
  intros Hnz Hf [left [HL DL]] [right [HR DR]] Hs.
  destruct (pair_total M f s) as [row Hrow]. exists row. split;[exact Hrow|].
  apply (trace_derives_binary M raw_source_rules row left right DL DR),raw_source_trace_binary.
  exists f,s,a,b,u,v. repeat first [assumption|split].
Qed.

Theorem raw_source_image_universal M x g f u b c v s :
  universal_graph M x g f -> raw_source_image M g u -> raw_binder_renaming M x b c ->
  numerical_renaming M u b c (succM M x) (succM M (zeroM M)) v ->
  sf_relation M SFAll v (zeroM M) s -> raw_source_image M f s.
Proof.
  intros Hf [previous [HP DP]] HB HR HS.
  destruct (pair_total M f s) as [row Hrow]. exists row. split;[exact Hrow|].
  apply (trace_derives_unary M raw_source_rules row previous DP),raw_source_trace_unary.
  exists f,s,x,g,u,b,c,v. repeat first [assumption|split].
Qed.

Theorem raw_source_image_total M f : exists s,raw_source_image M f s.
Proof.
  revert f. apply (named_formula_code_induction M (fun f=>exists s,raw_source_image M f s)).
  - apply raw_source_image_exists_definable.
  - destruct (sf_relation_total M SFImpl (zeroM M) (zeroM M)) as [s HS].
    exists s. apply raw_source_image_base. now left.
  - intros a b f HF. destruct (sf_relation_total M SFMember a b) as [s HS].
    exists s. apply raw_source_image_base. right;left. exists a,b. auto.
  - intros a b f HF. destruct (sf_relation_total M SFEqual a b) as [s HS].
    exists s. apply raw_source_image_base. right;right. exists a,b. auto.
  - intros a b f Hnz HF [u HU] [v HV]. destruct (sf_relation_total M SFImpl u v) as [s HS].
    exists s. exact (raw_source_image_implication M a b f u v s Hnz HF HU HV HS).
  - intros x g f HF [u HU]. destruct (raw_named_binder_image_total M x u) as [b [c [v [s [HB [HR HS]]]]]].
    exists s. exact (raw_source_image_universal M x g f u b c v s HF HU HB HR HS).
Qed.

Print Assumptions raw_source_image_formula_correct.
Print Assumptions raw_source_image_implication.
Print Assumptions raw_source_image_universal.
Print Assumptions raw_source_image_total.








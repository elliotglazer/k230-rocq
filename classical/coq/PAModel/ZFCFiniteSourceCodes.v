(** The twelve fixed source axioms, using the separate eight-tag full
    de Bruijn source syntax. This is distinct from the four-tag target
    templates in ZFCFiniteAxiomTemplates. No schemas or proof translation
    are claimed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs NumericalTheories SentenceBounds StandardModel
  SetFormulaCodes ZFCFiniteAxiomTemplates.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From Stdlib Require Import List.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint sf_expression {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) : code_expr :=
  match phi with
  | falsity => CEconst 0
  | atom P v =>
      match P return Vector.t sf_term (ZF_pred_ar P) -> code_expr with
      | elem => fun v => E_sf SFMember (CEconst (sf_index (Vector.hd v)))
          (CEconst (sf_index (Vector.hd (Vector.tl v))))
      | equal => fun v => E_sf SFEqual (CEconst (sf_index (Vector.hd v)))
          (CEconst (sf_index (Vector.hd (Vector.tl v))))
      end v
  | bin op a b => E_sf
      (match op with Conj => SFAnd | Disj => SFOr | Impl => SFImpl end)
      (sf_expression a) (sf_expression b)
  | quant q a => E_sf (match q with All => SFAll | Ex => SFEx end)
      (sf_expression a) (CEconst 0)
  end.

Theorem sf_expression_value {ff} env
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  code_value env (sf_expression phi) = sf_encode phi.
Proof.
  induction phi; cbn [sf_expression sf_encode].
  - reflexivity.
  - destruct P; rewrite sf_make_value; reflexivity.
  - rewrite sf_make_value, IHphi1, IHphi2. reflexivity.
  - rewrite sf_make_value, IHphi. reflexivity.
Qed.

Definition zfc_fixed_source_expression tag := sf_expression (zfc_fixed_source tag).
Definition zfc_fixed_source_code tag := sf_encode (zfc_fixed_source tag).

Lemma zfc_fixed_source_expression_value env tag :
  code_value env (zfc_fixed_source_expression tag) = zfc_fixed_source_code tag.
Proof. apply sf_expression_value. Qed.

Definition zfc_source_graph M tag z :=
  code_relation M (fun _ => zeroM M) (zfc_fixed_source_expression tag) z.
Definition zfc_source_graph_formula tag (z : pa_term) : pa_form :=
  code_formula (zfc_fixed_source_expression tag) (fun _ => zero) z.

Lemma zfc_source_graph_formula_correct M tag rho z :
  holds M rho (zfc_source_graph_formula tag z) <->
  zfc_source_graph M tag (evalM M rho z).
Proof. apply code_formula_correct. Qed.

Lemma zfc_source_graph_total M tag : exists z, zfc_source_graph M tag z.
Proof. apply code_relation_total. Qed.

Lemma zfc_source_graph_functional M tag z z' :
  zfc_source_graph M tag z -> zfc_source_graph M tag z' -> z = z'.
Proof. apply code_relation_functional. Qed.

Fixpoint zfc_source_disjunction tags (z : pa_term) : pa_form :=
  match tags with
  | [] => falsity
  | tag :: tags => zfc_source_graph_formula tag z ∨ zfc_source_disjunction tags z
  end.

Lemma zfc_source_disjunction_correct M rho tags z :
  holds M rho (zfc_source_disjunction tags z) <->
  exists tag, In tag tags /\ zfc_source_graph M tag (evalM M rho z).
Proof.
  induction tags as [|tag tags IH]; cbn [zfc_source_disjunction].
  - split; [contradiction|intros [i [H _]]; contradiction].
  - rewrite holds_or, zfc_source_graph_formula_correct, IH.
    split.
    + intros [H|[i [Hi H]]].
      * exists tag. split; [now left|exact H].
      * exists i. split; [now right|exact H].
    + intros [i [[<-|Hi] H]].
      * now left.
      * right. now exists i.
Qed.

Definition zfc_fixed_source_formula (z : pa_term) : pa_form :=
  zfc_source_disjunction zfc_fixed_tags z.

Theorem zfc_fixed_source_formula_correct M rho z :
  holds M rho (zfc_fixed_source_formula z) <->
  exists tag, zfc_source_graph M tag (evalM M rho z).
Proof.
  unfold zfc_fixed_source_formula. rewrite zfc_source_disjunction_correct.
  split; [intros [tag [_ H]]; now exists tag|].
  intros [tag H]. exists tag. split; [apply zfc_fixed_tags_complete|exact H].
Qed.

Lemma zfc_fixed_source_formula_unary : bounded 1 (zfc_fixed_source_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

(** Only the fixed source axioms. The full StandardZFC theory also needs its
    closed Separation and Replacement instances and a source proof calculus. *)
Definition ZFCFixedSourceTheory : NumericalTheory :=
  {| theory_formula := zfc_fixed_source_formula $0;
     theory_bounded := zfc_fixed_source_formula_unary |}.

Theorem ZFCFixedSourceTheory_axiom M z :
  theory_axiom M ZFCFixedSourceTheory z <-> exists tag, zfc_source_graph M tag z.
Proof. apply zfc_fixed_source_formula_correct. Qed.

Corollary ZFCFixedSourceTheory_standard_axiom z :
  theory_axiom natModel ZFCFixedSourceTheory z <->
  exists tag, z = sf_encode (zfc_fixed_source tag).
Proof.
  rewrite ZFCFixedSourceTheory_axiom. unfold zfc_source_graph.
  setoid_rewrite code_relation_natModel.
  setoid_rewrite zfc_fixed_source_expression_value. reflexivity.
Qed.

Print Assumptions sf_expression_value.
Print Assumptions zfc_source_graph_formula_correct.
Print Assumptions zfc_source_graph_total.
Print Assumptions zfc_source_graph_functional.
Print Assumptions zfc_fixed_source_formula_correct.
Print Assumptions zfc_fixed_source_formula_unary.
Print Assumptions ZFCFixedSourceTheory_axiom.
Print Assumptions ZFCFixedSourceTheory_standard_axiom.

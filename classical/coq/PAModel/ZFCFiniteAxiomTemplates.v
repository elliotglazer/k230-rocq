(** Fixed axioms of the conventional source theory, with numerical templates.
    The ten minZF axioms are imported definitions. Foundation and Choice below
    reproduce the pinned RegCon.MinZF and ZFC.Z_wo definitions; the accompanying
    source audit checks those bodies against the frozen reference sources.
    This is a finite list of TARGET codes. Separation and Replacement are not
    recognized. The machine's four-tag code is not a faithful code for the full
    source syntax: code 1 is both falsity and Wel(0,0), and code 0 is both truth
    and Wim(0,0). No injectivity, semantic preservation, or full StandardZFC
    NumericalTheory is asserted here. A distinct source encoding and a checked
    interpretation into these target codes remain necessary. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs CodeExpressions SentenceBounds
  QuotientAtomTemplates NumericalTheories StandardModel.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import List Bool Lia PeanoNat.
Import ListNotations.
Unset Implicit Arguments.

Definition source_foundation : set_form :=
  ∀ (∃ $0 ∈' $1) → ∃ ($0 ∈' $1 ∧ ∀ ($0 ∈' $1 → ¬ ($0 ∈' $2))).

Definition source_choice_matrix (x : set_term) : set_form :=
  (∀ ($0 ∈' x`[↑] → ∃ ($0 ∈' $1))) →
  (∀ ($0 ∈' x`[↑] → ∀ ($0 ∈' x`[↑]`[↑] → ¬ ($1 ≡' $0) → ¬ ∃ ($0 ∈' $2 ∧ $0 ∈' $1)))) →
  ∃ ∀ ($0 ∈' x`[↑]`[↑] → ∃ ($0 ∈' $1 ∧ $0 ∈' $2 ∧ ∀ ($0 ∈' $2 → $0 ∈' $3 → $0 ≡' $1))).

Definition source_choice : set_form := ∀ source_choice_matrix $0.

Inductive zfc_fixed_axiom : Type :=
| ZFCRefl | ZFCSym | ZFCTrans | ZFCEqElem
| ZFCExt | ZFCEmpty | ZFCPair | ZFCUnion | ZFCPower | ZFCOmega
| ZFCFoundation | ZFCChoice.

Definition zfc_fixed_source (tag : zfc_fixed_axiom) : set_form :=
  match tag with
  | ZFCRefl => ax_refl'
  | ZFCSym => ax_sym'
  | ZFCTrans => ax_trans'
  | ZFCEqElem => ax_eq_elem'
  | ZFCExt => ax_ext'
  | ZFCEmpty => ax_eset'
  | ZFCPair => ax_pair'
  | ZFCUnion => ax_union'
  | ZFCPower => ax_power'
  | ZFCOmega => ax_om'
  | ZFCFoundation => source_foundation
  | ZFCChoice => source_choice
  end.

Definition zfc_fixed_tags : list zfc_fixed_axiom :=
  [ZFCRefl; ZFCSym; ZFCTrans; ZFCEqElem;
   ZFCExt; ZFCEmpty; ZFCPair; ZFCUnion; ZFCPower; ZFCOmega;
   ZFCFoundation; ZFCChoice].

Lemma zfc_fixed_tags_complete tag : In tag zfc_fixed_tags.
Proof. destruct tag; cbn; tauto. Qed.

Definition zfc_fixed_template_from (fresh : code_expr) (tag : zfc_fixed_axiom) :=
  template_set_formula (fun _ => CEconst 0) fresh (zfc_fixed_source tag).

(** Each source axiom is closed. Binder names are 0,1,... along each branch;
    names may be reused in disjoint branches. *)
Definition zfc_fixed_template := zfc_fixed_template_from (CEconst 0).

Fixpoint code_expr_closedb (e : code_expr) : bool :=
  match e with
  | CEconst _ => true
  | CEvar _ => false
  | CEadd a b | CEmul a b | CEpair a b => code_expr_closedb a && code_expr_closedb b
  end.

Lemma zfc_fixed_template_closed tag :
  code_expr_closedb (zfc_fixed_template tag) = true.
Proof. destruct tag; vm_compute; reflexivity. Qed.

Definition set_term_boundb k (t : set_term) : bool :=
  match t with var i => Nat.ltb i k | func f _ => match f with end end.

Fixpoint set_formula_boundb {ff} k
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : bool :=
  match phi with
  | falsity => true
  | atom _ args => vector_allb (set_term_boundb k) args
  | bin _ a b => set_formula_boundb k a && set_formula_boundb k b
  | quant _ a => set_formula_boundb (S k) a
  end.

Lemma set_term_boundb_sound k t : set_term_boundb k t = true -> bounded_t k t.
Proof. destruct t as [i|[]]; cbn. intro H. constructor. now apply Nat.ltb_lt. Qed.

Lemma set_formula_boundb_sound {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall k, set_formula_boundb k phi = true -> bounded k phi.
Proof.
  induction phi; intros k; cbn.
  - intros _. constructor.
  - rewrite vector_allb_true. intro H. constructor.
    intros u Hu. apply set_term_boundb_sound. now apply H.
  - rewrite Bool.andb_true_iff. intros [Ha Hb]. constructor; auto.
  - intro H. constructor. now apply IHphi.
Qed.

Lemma zfc_fixed_source_closed tag : bounded 0 (zfc_fixed_source tag).
Proof. apply set_formula_boundb_sound. destruct tag; vm_compute; reflexivity. Qed.

(** An independent direct natural-number traversal of the source syntax.
    The graph template is checked against this traversal structurally,
    without expanding the enormous resulting Cantor-pairing numerals. *)
Definition named_term (env : nat -> nat) (t : set_term) : nat :=
  match t with
  | var i => env i
  | func f _ => match f with end
  end.

Fixpoint named_source_code {ff} (env : nat -> nat) (fresh : nat)
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : nat :=
  match phi with
  | falsity => 1
  | atom P v =>
      match P return Vector.t set_term (ar_preds P) -> nat with
      | elem => fun v => KCode230.wel (named_term env (Vector.hd v))
          (named_term env (Vector.hd (Vector.tl v)))
      | equal => fun v => KCode230.weq (named_term env (Vector.hd v))
          (named_term env (Vector.hd (Vector.tl v)))
      end v
  | bin Conj a b => KCode230.wa (named_source_code env fresh a) (named_source_code env fresh b)
  | bin Disj a b => KCode230.wim (KCode230.wn (named_source_code env fresh a))
      (named_source_code env fresh b)
  | bin Impl a b => KCode230.wim (named_source_code env fresh a) (named_source_code env fresh b)
  | quant All a => KCode230.wal fresh (named_source_code (fresh .: env) (S fresh) a)
  | quant Ex a => KCode230.wex fresh (named_source_code (fresh .: env) (S fresh) a)
  end.

Lemma template_term_value rho env t :
  code_value rho (template_term env t) = named_term (fun i => code_value rho (env i)) t.
Proof. destruct t as [i|[]]; reflexivity. Qed.

Local Opaque KCode230.P KCode230.wim KCode230.wel KCode230.weq
  KCode230.wal KCode230.wn KCode230.wa KCode230.wex.

Lemma named_term_ext env env' t :
  (forall i, env i = env' i) -> named_term env t = named_term env' t.
Proof. destruct t as [i|[]]; cbn. auto. Qed.

Lemma named_source_code_ext {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) env env' fresh :
  (forall i, env i = env' i) ->
  named_source_code env fresh phi = named_source_code env' fresh phi.
Proof.
  induction phi in env,env',fresh |- *; intro H.
  - reflexivity.
  - destruct P; cbn [named_source_code];
      rewrite (named_term_ext _ _ _ H), (named_term_ext _ _ _ H); reflexivity.
  - destruct b0; cbn [named_source_code];
      rewrite (IHphi1 env env' fresh H), (IHphi2 env env' fresh H); reflexivity.
  - destruct q; cbn [named_source_code]; f_equal; apply IHphi;
      intros [|i]; cbn; auto.
Qed.

Theorem template_source_value {ff} rho env fresh
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  code_value rho (template_set_formula env fresh phi) =
  named_source_code (fun i => code_value rho (env i)) (code_value rho fresh) phi.
Proof.
  induction phi in env,fresh |- *.
  - reflexivity.
  - destruct P; cbn [template_set_formula named_source_code].
    + rewrite code_value_wel, !template_term_value. reflexivity.
    + rewrite code_value_weq, !template_term_value. reflexivity.
  - destruct b0; cbn [template_set_formula named_source_code].
    + rewrite code_value_wa, IHphi1, IHphi2. reflexivity.
    + unfold E_or. rewrite code_value_wim, code_value_wn, IHphi1, IHphi2. reflexivity.
    + rewrite code_value_wim, IHphi1, IHphi2. reflexivity.
  - destruct q; cbn [template_set_formula named_source_code].
    + rewrite code_value_wal, IHphi. cbn [code_value].
      replace (code_value rho fresh + 1) with (S (code_value rho fresh)) by lia.
      f_equal. apply named_source_code_ext. intros [|i]; reflexivity.
    + rewrite code_value_wex, IHphi. cbn [code_value].
      replace (code_value rho fresh + 1) with (S (code_value rho fresh)) by lia.
      f_equal. apply named_source_code_ext. intros [|i]; reflexivity.
Qed.

Definition zfc_fixed_code tag := named_source_code (fun _ => 0) 0 (zfc_fixed_source tag).

Corollary zfc_fixed_template_value rho tag :
  code_value rho (zfc_fixed_template tag) = zfc_fixed_code tag.
Proof. apply template_source_value. Qed.

Definition zfc_fixed_graph M tag z :=
  code_relation M (fun _ => zeroM M) (zfc_fixed_template tag) z.

#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition zfc_fixed_graph_formula tag (z : term) : form :=
  code_formula (zfc_fixed_template tag) (fun _ => zero) z.

Lemma zfc_fixed_graph_formula_correct M tag rho z :
  holds M rho (zfc_fixed_graph_formula tag z) <->
  zfc_fixed_graph M tag (evalM M rho z).
Proof. apply code_formula_correct. Qed.

Lemma zfc_fixed_graph_total M tag : exists z, zfc_fixed_graph M tag z.
Proof. apply code_relation_total. Qed.

Lemma zfc_fixed_graph_functional M tag z z' :
  zfc_fixed_graph M tag z -> zfc_fixed_graph M tag z' -> z = z'.
Proof. apply code_relation_functional. Qed.

Fixpoint zfc_fixed_disjunction (tags : list zfc_fixed_axiom) (z : term) : form :=
  match tags with
  | [] => falsity
  | tag :: tags => zfc_fixed_graph_formula tag z ∨ zfc_fixed_disjunction tags z
  end.

Lemma zfc_fixed_disjunction_correct M rho tags z :
  holds M rho (zfc_fixed_disjunction tags z) <->
  exists tag, In tag tags /\ zfc_fixed_graph M tag (evalM M rho z).
Proof.
  induction tags as [|tag tags IH]; cbn [zfc_fixed_disjunction].
  - split; [contradiction|intros [i [H _]]; contradiction].
  - rewrite holds_or, zfc_fixed_graph_formula_correct, IH.
    split.
    + intros [H|[i [Hi H]]].
      * exists tag. split; [now left|exact H].
      * exists i. split; [now right|exact H].
    + intros [i [[<-|Hi] H]].
      * now left.
      * right. now exists i.
Qed.

Definition zfc_fixed_axiom_formula (z : term) : form :=
  zfc_fixed_disjunction zfc_fixed_tags z.

Theorem zfc_fixed_axiom_formula_correct M rho z :
  holds M rho (zfc_fixed_axiom_formula z) <->
  exists tag, zfc_fixed_graph M tag (evalM M rho z).
Proof.
  unfold zfc_fixed_axiom_formula. rewrite zfc_fixed_disjunction_correct.
  split; [intros [tag [_ H]]; now exists tag|].
  intros [tag H]. exists tag. split; [apply zfc_fixed_tags_complete|exact H].
Qed.

Lemma zfc_fixed_axiom_formula_unary : bounded 1 (zfc_fixed_axiom_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

(** A finite numerical theory of the translated target-code graphs. This name
    does not assert that the full source StandardZFC theory is recognized. *)
Definition ZFCFixedTheory : NumericalTheory :=
  {| theory_formula := zfc_fixed_axiom_formula $0;
     theory_bounded := zfc_fixed_axiom_formula_unary |}.

Theorem ZFCFixedTheory_axiom M z :
  theory_axiom M ZFCFixedTheory z <-> exists tag, zfc_fixed_graph M tag z.
Proof. apply zfc_fixed_axiom_formula_correct. Qed.

Corollary ZFCFixedTheory_standard_axiom z :
  theory_axiom natModel ZFCFixedTheory z <-> exists tag, z = zfc_fixed_code tag.
Proof.
  rewrite ZFCFixedTheory_axiom. unfold zfc_fixed_graph.
  setoid_rewrite code_relation_natModel. setoid_rewrite zfc_fixed_template_value.
  reflexivity.
Qed.

Print Assumptions template_source_value.
Print Assumptions zfc_fixed_template_value.
Print Assumptions zfc_fixed_axiom_formula_correct.
Print Assumptions zfc_fixed_axiom_formula_unary.
Print Assumptions ZFCFixedTheory_axiom.
Print Assumptions zfc_fixed_source_closed.
Print Assumptions ZFCFixedTheory_standard_axiom.
Print Assumptions zfc_fixed_graph_total.
Print Assumptions zfc_fixed_graph_functional.
Print Assumptions zfc_fixed_template_closed.

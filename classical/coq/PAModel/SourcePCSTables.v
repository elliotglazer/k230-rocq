(** Internally finite tables with exactly the pcs entries. The membership
    specification is extensional; construction keeps both signs and uses
    ordered concatenation/cons. No external finite-list premise is used. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs Pairing
  SetFormulaCodes SetCodeDescent SourceBounded NumericalContexts NumericalEnvironments ContextCombination
  SourceRelativization SourcePCSPieces SourceQuantifierPieceInversion.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_pcs_table M domain f n b c l := forall entry,
  context_member M b c l entry <-> source_pcs_entry M domain f n entry.
Definition source_pcs_table_formula (domain f n b c l:term) : form :=
  ∀ ((context_member_formula b`[↑] c`[↑] l`[↑] $0 →
       source_pcs_entry_formula domain`[↑] f`[↑] n`[↑] $0) ∧
     (source_pcs_entry_formula domain`[↑] f`[↑] n`[↑] $0 →
       context_member_formula b`[↑] c`[↑] l`[↑] $0)).
Local Opaque holds context_member_formula source_pcs_entry_formula.

Theorem source_pcs_table_formula_correct M rho domain f n b c l :
  holds M rho (source_pcs_table_formula domain f n b c l) <->
  source_pcs_table M (evalM M rho domain) (evalM M rho f) (evalM M rho n)
    (evalM M rho b) (evalM M rho c) (evalM M rho l).
Proof.
  unfold source_pcs_table_formula,source_pcs_table.
  setoid_rewrite holds_all. setoid_rewrite holds_and. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct. setoid_rewrite source_pcs_entry_formula_correct.
  unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.

Lemma source_pcs_table_empty M domain f n :
  (f=zeroM M \/ sf_invalid M f \/ exists h a b,(h=SFMember \/ h=SFEqual) /\ sf_relation M h a b f) ->
  source_pcs_table M domain f n (zeroM M) (zeroM M) (zeroM M).
Proof.
  intros HF entry. split.
  - intro H. exfalso. exact (context_empty M (zeroM M) (zeroM M) entry H).
  - intro H. exfalso. exact (source_pcs_entry_leaf_none M domain f n entry HF H).
Qed.

Definition source_pcs_table_total_property M domain f :=
  forall n,exists b c l,source_pcs_table M domain f n b c l.
Definition source_pcs_table_total_formula : form :=
  ∀∃∃∃ source_pcs_table_formula $5 $4 $3 $2 $1 $0.
Local Opaque source_pcs_table_formula.
Lemma source_pcs_table_total_definable M domain :
  Definable1 M (source_pcs_table_total_property M domain).
Proof.
  exists source_pcs_table_total_formula,(domain .: fun _=>zeroM M). intro f.
  unfold source_pcs_table_total_formula,source_pcs_table_total_property.
  setoid_rewrite holds_all. repeat setoid_rewrite holds_ex.
  setoid_rewrite source_pcs_table_formula_correct. reflexivity.
Qed.

Theorem source_pcs_table_total M domain f n : exists b c l,source_pcs_table M domain f n b c l.
Proof.
  revert f n. apply (sf_code_induction M (source_pcs_table_total_property M domain)).
  - apply source_pcs_table_total_definable.
  - intro n. exists (zeroM M),(zeroM M),(zeroM M). apply source_pcs_table_empty. now left.
  - intros f HF n. exists (zeroM M),(zeroM M),(zeroM M). apply source_pcs_table_empty. right;now left.
  - intros a b f HF n. exists (zeroM M),(zeroM M),(zeroM M). apply source_pcs_table_empty.
    right;right. exists SFMember,a,b. split;[now left|exact HF].
  - intros a b f HF n. exists (zeroM M),(zeroM M),(zeroM M). apply source_pcs_table_empty.
    right;right. exists SFEqual,a,b. split;[now right|exact HF].
  - intros h a b f HH HF IHa IHb n.
    destruct (IHa n) as (ab & ac & al & HA). destruct (IHb n) as (bb & bc & bl & HB).
    destruct (context_union_total M ab ac al bb bc bl) as (u & v & l & HU).
    exists u,v,l. intro entry. rewrite (proj2 HU entry),(HA entry),(HB entry).
    symmetry. exact (source_pcs_entry_binary M domain h a b f n entry HH HF).
  - intros h a f HH HF IH n.
    destruct (IH (succM M n)) as (b & c & l & HT).
    destruct (source_relativization_total M domain a) as [rel HR].
    destruct (sf_relation_total M SFImpl rel (zeroM M)) as [neg HN].
    destruct (pair_total M n rel) as [posentry HPos]. destruct (pair_total M n neg) as [negentry HNeg].
    destruct (environment_cons_total M b c l negentry) as (nb & nc & nl & HNC).
    destruct (environment_cons_total M nb nc nl posentry) as (pb & pc & pl & HPC).
    exists pb,pc,pl. intro entry.
    rewrite (context_member_cons M nb nc nl posentry pb pc pl entry HPC),
      (context_member_cons M b c l negentry nb nc nl entry HNC),(HT entry).
    symmetry. exact (source_pcs_entry_quantifier M domain h a f n rel neg posentry negentry entry HH HF HR HN HPos HNeg).
Qed.

Theorem source_pcs_table_bounded M domain f n b c l :
  source_bounded M domain (code_numeral M 1) -> source_bounded M f n ->
  source_pcs_table M domain f n b c l -> forall entry,context_member M b c l entry ->
  exists k piece,pair_graph M k piece entry /\ source_bounded M piece (succM M k).
Proof.
  intros HD HF HT entry HE.
  exact (source_pcs_entry_bounded M domain f n entry HD HF (proj1 (HT entry) HE)).
Qed.

Print Assumptions source_pcs_table_formula_correct.
Print Assumptions source_pcs_table_total.
Print Assumptions source_pcs_table_bounded.

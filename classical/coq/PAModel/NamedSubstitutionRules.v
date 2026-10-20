(** Partial, capture-avoiding substitution for the machine's named four-tag
    syntax. Code 0 is the closed truth leaf. Code 1 is the membership atom
    Wel(0,0), so substituting for name 0 may change it. There is no special
    immutable-falsity branch. All codes and trace lengths are model values.

    The operation stops at a binder for the source name. At any other binder
    it requires a name distinct from the replacement name; it does not rename
    a colliding binder. Identity substitution is always permitted. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  CodeDescent CodeTags CodeTuples NumericalProofs NumericalTraces SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition named_replace (M : Model) (x y a b : carrier M) : Prop :=
  (a=x /\ b=y) \/ (a<>x /\ b=a).
Definition named_replace_formula (x y a b : term) : form :=
  ((a == x) ∧ (b == y)) ∨ ((¬ (a == x)) ∧ (b == a)).
Lemma named_replace_formula_correct M rho x y a b :
  holds M rho (named_replace_formula x y a b) <->
  named_replace M (evalM M rho x) (evalM M rho y) (evalM M rho a) (evalM M rho b).
Proof. reflexivity. Qed.
Lemma named_replace_total M x y a : exists b, named_replace M x y a b.
Proof.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) a x) as [H|H].
  - exists y. now left.
  - exists a. now right.
Qed.
Lemma named_replace_functional M x y a b c :
  named_replace M x y a b -> named_replace M x y a c -> b=c.
Proof. unfold named_replace;intros [[-> ->]|[H ->]] [[E ->]|[H' ->]];congruence. Qed.
Lemma named_replace_identity M x a b : named_replace M x x a b -> b=a.
Proof. unfold named_replace;intros [[-> ->]|[_ ->]];reflexivity. Qed.

Definition named_atom_tag (eq : bool) : nat := if eq then 3 else 1.
Definition named_sub_row M f x y v r :=
  tuple7_graph M f x y (zeroM M) (zeroM M) (zeroM M) v r.
Definition named_sub_row_formula (f x y v r : term) :=
  tuple7_formula f x y zero zero zero v r.
Lemma named_sub_row_correct M rho f x y v r :
  holds M rho (named_sub_row_formula f x y v r) <->
  named_sub_row M (evalM M rho f) (evalM M rho x) (evalM M rho y)
    (evalM M rho v) (evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.
Lemma named_sub_row_total M f x y v : exists r,named_sub_row M f x y v r.
Proof. apply tuple7_total. Qed.
Lemma named_sub_row_injective M f x y v f' x' y' v' r :
  named_sub_row M f x y v r -> named_sub_row M f' x' y' v' r ->
  f=f' /\ x=x' /\ y=y' /\ v=v'.
Proof. intros H H'. pose proof (tuple7_injective M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H');tauto. Qed.

Definition named_sub_stop M f x y :=
  x=y \/ f=zeroM M \/ exists a,tagged_pair_graph M 2 x a f.
Definition named_sub_stop_formula (f x y : term) : form :=
  (x == y) ∨ ((f == zero) ∨ ∃ tagged_pair_formula 2 x`[↑] $0 f`[↑]).
Local Opaque holds tagged_pair_formula.
Lemma named_sub_stop_correct M rho f x y :
  holds M rho (named_sub_stop_formula f x y) <->
  named_sub_stop M (evalM M rho f) (evalM M rho x) (evalM M rho y).
Proof.
  unfold named_sub_stop_formula,named_sub_stop.
  repeat setoid_rewrite holds_or. setoid_rewrite holds_ex.
  setoid_rewrite tagged_pair_formula_correct.
  unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.

Definition named_sub_atom M eq f x y v := exists a b a' b',
  tagged_pair_graph M (named_atom_tag eq) a b f /\
  named_replace M x y a a' /\ named_replace M x y b b' /\
  tagged_pair_graph M (named_atom_tag eq) a' b' v.
Definition named_sub_atom_formula eq (f x y v : term) : form :=
  ∃∃∃∃ (tagged_pair_formula (named_atom_tag eq) $3 $2 (lift4 f) ∧
    named_replace_formula (lift4 x) (lift4 y) $3 $1 ∧
    named_replace_formula (lift4 x) (lift4 y) $2 $0 ∧
    tagged_pair_formula (named_atom_tag eq) $1 $0 (lift4 v)).
Local Opaque named_replace_formula.
Lemma named_sub_atom_correct M rho eq f x y v :
  holds M rho (named_sub_atom_formula eq f x y v) <->
  named_sub_atom M eq (evalM M rho f) (evalM M rho x) (evalM M rho y) (evalM M rho v).
Proof.
  unfold named_sub_atom_formula,named_sub_atom.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite named_replace_formula_correct. try setoid_rewrite lift4_correct.
  split;intros [a [b [a' [b' H]]]];exists a,b,a',b';tauto.
Qed.

Definition named_sub_leaf M f x y v :=
  (named_sub_stop M f x y /\ v=f) \/
  (x<>y /\ (named_sub_atom M false f x y v \/ named_sub_atom M true f x y v)).
Definition named_sub_leaf_formula (f x y v : term) : form :=
  (named_sub_stop_formula f x y ∧ (v == f)) ∨
  ((¬ (x == y)) ∧ (named_sub_atom_formula false f x y v ∨ named_sub_atom_formula true f x y v)).
Local Opaque named_sub_stop_formula named_sub_atom_formula.
Lemma named_sub_leaf_correct M rho f x y v :
  holds M rho (named_sub_leaf_formula f x y v) <->
  named_sub_leaf M (evalM M rho f) (evalM M rho x) (evalM M rho y) (evalM M rho v).
Proof.
  unfold named_sub_leaf_formula,named_sub_leaf.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or.
  setoid_rewrite named_sub_stop_correct. setoid_rewrite named_sub_atom_correct.
  reflexivity.
Qed.

Definition named_sub_base M r := exists f x y v,
  named_sub_row M f x y v r /\ named_sub_leaf M f x y v.
Definition named_sub_base_formula : form :=
  ∃∃∃∃ (named_sub_row_formula $3 $2 $1 $0 $4 ∧ named_sub_leaf_formula $3 $2 $1 $0).
Local Opaque named_sub_row_formula named_sub_leaf_formula.
Lemma named_sub_base_correct M rho r :
  holds M (r .: rho) named_sub_base_formula <-> named_sub_base M r.
Proof.
  unfold named_sub_base_formula,named_sub_base.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite named_sub_row_correct. setoid_rewrite named_sub_leaf_correct. reflexivity.
Qed.

Definition named_sub_unary_case M f x y v p := exists a b w,
  x<>y /\ a<>x /\ a<>y /\ tagged_pair_graph M 2 a b f /\
  named_sub_row M b x y w p /\ tagged_pair_graph M 2 a w v.
Definition named_sub_unary_case_formula (f x y v p : term) : form :=
  ∃∃∃ ((¬ (lift3 x == lift3 y)) ∧ (¬ ($2 == lift3 x)) ∧ (¬ ($2 == lift3 y)) ∧
    tagged_pair_formula 2 $2 $1 (lift3 f) ∧
    named_sub_row_formula $1 (lift3 x) (lift3 y) $0 (lift3 p) ∧
    tagged_pair_formula 2 $2 $0 (lift3 v)).
Lemma named_sub_unary_case_correct M rho f x y v p :
  holds M rho (named_sub_unary_case_formula f x y v p) <->
  named_sub_unary_case M (evalM M rho f) (evalM M rho x)
    (evalM M rho y) (evalM M rho v) (evalM M rho p).
Proof.
  unfold named_sub_unary_case_formula,named_sub_unary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite code_holds_neq. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite named_sub_row_correct. try setoid_rewrite lift3_correct.
  split;intros [a [b [w H]]];exists a,b,w;tauto.
Qed.
Definition named_sub_unary M r p := exists f x y v,
  named_sub_row M f x y v r /\ named_sub_unary_case M f x y v p.
Definition named_sub_unary_formula : form :=
  ∃∃∃∃ (named_sub_row_formula $3 $2 $1 $0 $4 ∧ named_sub_unary_case_formula $3 $2 $1 $0 $5).
Local Opaque named_sub_unary_case_formula.
Lemma named_sub_unary_correct M rho r p :
  holds M (r .: p .: rho) named_sub_unary_formula <-> named_sub_unary M r p.
Proof.
  unfold named_sub_unary_formula,named_sub_unary.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite named_sub_row_correct. setoid_rewrite named_sub_unary_case_correct. reflexivity.
Qed.

Definition named_sub_binary_case M f x y v p q := exists a b a' b',
  x<>y /\ f<>zeroM M /\ tagged_pair_graph M 0 a b f /\
  named_sub_row M a x y a' p /\ named_sub_row M b x y b' q /\
  tagged_pair_graph M 0 a' b' v.
Definition named_sub_binary_case_formula (f x y v p q : term) : form :=
  ∃∃∃∃ ((¬ (lift4 x == lift4 y)) ∧ (¬ (lift4 f == zero)) ∧
    tagged_pair_formula 0 $3 $2 (lift4 f) ∧
    named_sub_row_formula $3 (lift4 x) (lift4 y) $1 (lift4 p) ∧
    named_sub_row_formula $2 (lift4 x) (lift4 y) $0 (lift4 q) ∧
    tagged_pair_formula 0 $1 $0 (lift4 v)).
Lemma named_sub_binary_case_correct M rho f x y v p q :
  holds M rho (named_sub_binary_case_formula f x y v p q) <->
  named_sub_binary_case M (evalM M rho f) (evalM M rho x)
    (evalM M rho y) (evalM M rho v) (evalM M rho p) (evalM M rho q).
Proof.
  unfold named_sub_binary_case_formula,named_sub_binary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite code_holds_neq. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite named_sub_row_correct. try setoid_rewrite lift4_correct.
  split;intros [a [b [a' [b' H]]]];exists a,b,a',b';tauto.
Qed.
Definition named_sub_binary M r p q := exists f x y v,
  named_sub_row M f x y v r /\ named_sub_binary_case M f x y v p q.
Definition named_sub_binary_formula : form :=
  ∃∃∃∃ (named_sub_row_formula $3 $2 $1 $0 $4 ∧ named_sub_binary_case_formula $3 $2 $1 $0 $5 $6).
Local Opaque named_sub_binary_case_formula.
Lemma named_sub_binary_correct M rho r p q :
  holds M (r .: p .: q .: rho) named_sub_binary_formula <-> named_sub_binary M r p q.
Proof.
  unfold named_sub_binary_formula,named_sub_binary.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite named_sub_row_correct. setoid_rewrite named_sub_binary_case_correct. reflexivity.
Qed.

Definition named_sub_rules : NumericalRules.
Proof.
  refine {|rule_base_formula:=named_sub_base_formula;
    rule_unary_formula:=named_sub_unary_formula;
    rule_binary_formula:=named_sub_binary_formula|};
    apply formula_boundb_sound;vm_compute;reflexivity.
Defined.
Lemma named_sub_rule_base M r : trace_base M named_sub_rules r <-> named_sub_base M r.
Proof. apply named_sub_base_correct. Qed.
Lemma named_sub_rule_unary M r p : trace_unary M named_sub_rules r p <-> named_sub_unary M r p.
Proof. apply named_sub_unary_correct. Qed.
Lemma named_sub_rule_binary M r p q : trace_binary M named_sub_rules r p q <-> named_sub_binary M r p q.
Proof. apply named_sub_binary_correct. Qed.

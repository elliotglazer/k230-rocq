(** Composition of finite arithmetic code-expression templates. It changes
    expression holes only and introduces no source-language syntax. *)
From PAModel Require Import Model CodeExpressions.
Unset Implicit Arguments.
Fixpoint code_plug (sigma:nat->code_expr)(e:code_expr):code_expr :=
 match e with
 | CEconst n=>CEconst n | CEvar i=>sigma i
 | CEadd a b=>CEadd(code_plug sigma a)(code_plug sigma b)
 | CEmul a b=>CEmul(code_plug sigma a)(code_plug sigma b)
 | CEpair a b=>CEpair(code_plug sigma a)(code_plug sigma b)
 end.
Theorem code_relation_plug M rho values sigma e out :
 (forall i,code_relation M rho(sigma i)(values i)) ->
 (code_relation M rho(code_plug sigma e)out <->code_relation M values e out).
Proof.
 intro HH. induction e in out|-*;cbn[code_plug code_relation].
 - reflexivity.
 - split;intro H;[exact(code_relation_functional M(sigma i)rho out(values i) H(HH i))|now subst out].
 - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
 - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
 - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
Qed.
Print Assumptions code_relation_plug.

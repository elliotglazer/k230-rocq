(** The sole finite geometry law used after opening an old common level.
    Its full ordinary source proof is constructed, not assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceCofinalExtensionShell SourceZFRProvability.
Unset Implicit Arguments.
Definition source_cofinal_successor_law M start count Ks Lb law :=exists
 ordinals cover oldmember oldlevel newmember exD bodyD bodyY kmem ordinal level pair left subset member right tail4 tail3 tail2 tail1,
 source_cofinal_extension_shell M(succM M(succM M Ks))(succM M(succM M Lb))
 (code_numeral M 1)(zeroM M)(addM M count(succM M(succM M start)))
 ordinals cover oldmember oldlevel newmember exD bodyD bodyY kmem ordinal level pair left subset member right tail4 tail3 tail2 tail1 law.
Theorem source_zfr_cofinal_successor_law M start count Ks Lb:exists law,
 source_cofinal_successor_law M start count Ks Lb law /\source_zfr_provable M law.
Proof.
 destruct(source_zfr_cofinal_extension_shell M(succM M(succM M Ks))(succM M(succM M Lb))
 (code_numeral M 1)(zeroM M)(addM M count(succM M(succM M start))))as
 (ordinals&cover&oldmember&oldlevel&newmember&exD&bodyD&bodyY&kmem&ordinal&level&pair&left&subset&member&right&tail4&tail3&tail2&tail1&law&H&PP).
 exists law. split;[|exact PP]. exists ordinals,cover,oldmember,oldlevel,newmember,exD,bodyD,bodyY,kmem,ordinal,level,pair,left,subset,member,right,tail4,tail3,tail2,tail1. exact H.
Qed.
Print Assumptions source_zfr_cofinal_successor_law.

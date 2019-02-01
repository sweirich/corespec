This repository must be built with Coq 8.8.

For full installation instructions, see LIBRARIES.md.

To build the Coq, run `make coq`.

This work checks with Coq's native theory -- it includes no Axioms or other
extensions.

Libraries (not language specific)
* dep_prog.v     - support for dependently-typed programming in Coq
* fset_facts.v   - lemmas about finite sets
* imports.v      - external libraries (such as ssreflect) and global settings
* tactics.v      - (our own) general purpose tactics & solvers
* utils.v        - auxiliary definitions
* notations.v    - make things pretty

Syntactic definitions
* ett.ott        - source definitions in OTT
* ett_ott.v      - Coq definitions from OTT  [generated]
* ett_inf.v      - Coq definitions & lemmas from lngen [generated]
* ett_inf_tc.v   - ett_inf plus typeclasses [not used]
* ett_inf_cs.v   - ett_inf plus canonical structures
* ett_ind.v      - induction scheme, gather_atoms
                   more syntactic infrastructure results
				   
Example concrete signature

* fix_typing.v   - defines toplevel signature to include fixed point operator
* toplevel.v     - properties about the toplevel signatures

Properties about type-agnostic functions and relations:

* beta.v         - lc / subst for beta reduction relation
* ett_par.v      - facts about parallel reduction
* erase_syntax.v - interaction between erasure & syntactic functions
* ett_value.v    - Value/CoercedValue/Path/DataTy


Metatheory of Implicit Language
* ext_wf.v       - well-formedness of judgements, i.e. local closure, ctx wff
                   done, but could use more automation
* ext_context_fv.v - free variables contained in the context
* ett_erased.v   - properties of "role-ing" judgement
* ext_weak.v     - weakening lemma
* ext_subst.v    - substitution lemma
* ext_invert.v   - inversion lemmas, regularity   G |- a : A => G |- A : *
* ext_red.v      - preservation lemma (Par relation)
* ext_red_one.v  - facts about Values & reduction_in_one
* ext_consist.v  - consistency via confluence & reduction
* congruence. v  - congruence lemma for equality relation

New files for reasoning about roles and pattern matching

* ett_path.v     - terms headed by a constructor (F)
* ett_rename.v   - nominal treatment of axioms
* ett_roleling.v - metatheory of roleling judgement
* param.v        - reasoning about "param" Role operator
* pattern.v      - definitions and facts about patterns

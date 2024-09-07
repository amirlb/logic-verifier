(* Propositional Calculus *)

type pattern    (* Pattern for propositions joined with logical connectives *)
type inference  (* A valid logical inference  P1, ..., Pn |- Q *)

val metavar : int -> pattern
val pattern_and : pattern -> pattern -> pattern
val pattern_or : pattern -> pattern -> pattern
val pattern_implies : pattern -> pattern -> pattern
val pattern_iff : pattern -> pattern -> pattern
val pattern_not : pattern -> pattern
val consequence : pattern list -> pattern -> inference
val string_of_pattern : pattern -> string

(* Predicate Calculus *)

type variable   (* First-order variable *)
type predicate  (* Second-order variable, an open formula, or an atomic predicate *)
type formula    (* Predicate-calculus formula, either open or closed *)
type judgement  (* an assertion of the form  A1, ... An |- B *)

val make_builtin : arity:int -> name:string -> predicate
val predicate_of_formula : arity:int -> name:string -> (variable list -> formula) -> predicate
val string_of_predicate : predicate -> string

val apply : predicate -> variable list -> formula
val and_ : formula -> formula -> formula
val or_ : formula -> formula -> formula
val implies : formula -> formula -> formula
val iff : formula -> formula -> formula
val not_ : formula -> formula
val forall : name:string -> (variable -> formula) -> formula
val exists : name:string -> (variable -> formula) -> formula
val forall2 : arity:int -> name:string -> (predicate -> formula) -> formula
val equal_formula : formula -> formula -> bool
val string_of_formula : formula -> string

val judgement_premises : judgement -> formula Seq.t
val judgement_conclusion : judgement -> formula
val string_of_judgement : judgement -> string

val assuming : formula -> (judgement -> judgement) -> judgement         (* apply f to A |- A *)
val infer : inference -> judgement list -> formula -> judgement         (* apply this inference *)
val intro_forall : name:string -> (variable -> judgement) -> judgement  (* from |- A derive |- forall x. A *)
val elim_forall : variable -> judgement -> judgement                    (* from |- forall x. A derive |- A(y) *)
val intro_exists : name:string -> judgement -> judgement                (* from |- A(y) derive |- exists x. A *)
val elim_exists : variable -> formula -> judgement -> judgement         (* from A |- B derive exists x. A |- B *)
val intro_forall2 : arity:int -> name:string -> (predicate -> judgement) -> judgement
val elim_forall2 : predicate -> judgement -> judgement

module type OrderedPrintable = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
end

module Pattern : sig
  include OrderedPrintable
  val metavar : int -> t
  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val implies : t -> t -> t
  val iff : t -> t -> t
  val not_ : t -> t

  type inference
  val consequence : t list -> t -> inference
end

module Var1 : OrderedPrintable

module Var2 : OrderedPrintable
type arity = int

val make_builtin : arity -> string -> Var2.t

module Formula : sig
  include OrderedPrintable

  val apply : Var2.t -> Var1.t list -> t
  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val implies : t -> t -> t
  val iff : t -> t -> t
  val not_ : t -> t
  val forall : (Var1.t -> t) -> t
  val exists : (Var1.t -> t) -> t
  val forall2 : arity -> (Var2.t -> t) -> t
end

module Predicate : sig
  include OrderedPrintable
  val from_var : Var2.t -> t
  val from_formula : arity -> (Var1.t list -> Formula.t) -> t
end

module Verifier : sig
  type t  (* an assertion of the form  A1, ... An |- B *)

  val premises : t -> Formula.t Seq.t
  val conclusion : t -> Formula.t
  val to_string : t -> string

  val assuming : Formula.t -> (t -> t) -> t                   (* |- A => f (... |- A) *)
  val infer : Pattern.inference -> t list -> Formula.t -> t   (* apply this inference *)
  val intro_forall : (Var1.t -> t) -> t                       (* from |- A derive |- forall x. A *)
  val elim_forall : Var1.t -> t -> t                          (* from |- forall x. A derive |- A(y) *)
  val intro_exists : Var1.t -> t -> t                         (* from |- A(y) derive |- exists x. A *)
  val elim_exists : Var1.t -> Formula.t -> t -> t             (* from A |- B derive exists x. A |- B *)
  val intro_forall2 : arity -> (Var2.t -> t) -> t
  val elim_forall2 : Predicate.t -> t -> t
end

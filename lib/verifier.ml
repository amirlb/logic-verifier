module IntSet = Set.Make(Int)

module LogicOp = struct
  type 'a t =
    | And of 'a * 'a
    | Or of 'a * 'a
    | Implies of 'a * 'a
    | Iff of 'a * 'a
    | Not of 'a
  [@@deriving ord, map]

  let map2_unify f c1 c2 = match c1, c2 with
    | And(lhs1, rhs1), And(lhs2, rhs2) -> Some(And(f lhs1 lhs2, f rhs1 rhs2))
    | Or(lhs1, rhs1), Or(lhs2, rhs2) -> Some(Or(f lhs1 lhs2, f rhs1 rhs2))
    | Implies(lhs1, rhs1), Implies(lhs2, rhs2) -> Some(Implies(f lhs1 lhs2, f rhs1 rhs2))
    | Iff(lhs1, rhs1), Iff(lhs2, rhs2) -> Some(Iff(f lhs1 lhs2, f rhs1 rhs2))
    | Not(inner1), Not(inner2) -> Some(Not(f inner1 inner2))
    | _ -> None

  let collapse f = function
    | And(lhs, rhs) -> f lhs rhs
    | Or(lhs, rhs) -> f lhs rhs
    | Implies(lhs, rhs) -> f lhs rhs
    | Iff(lhs, rhs) -> f lhs rhs
    | Not(value) -> value

  let eval = function
    | And(lhs, rhs) -> lhs && rhs
    | Or(lhs, rhs) -> lhs || rhs
    | Implies(lhs, rhs) -> not lhs || rhs
    | Iff(lhs, rhs) -> lhs = rhs
    | Not(value) -> not value

  let to_string = function
    | And(lhs, rhs) -> Printf.sprintf "(%s ∧ %s)" lhs rhs
    | Or(lhs, rhs) -> Printf.sprintf "(%s ∨ %s)" lhs rhs
    | Implies(lhs, rhs) -> Printf.sprintf "(%s ⇒ %s)" lhs rhs
    | Iff(lhs, rhs) -> Printf.sprintf "(%s ⇔ %s)" lhs rhs
    | Not(inner) -> Printf.sprintf "¬%s" inner
end

module Pattern = struct
  type t =
    | MetaVar of int
    | Op of t LogicOp.t

  let evaluate assignment = 
    let rec go = function
      | MetaVar i -> assignment i
      | Op expr -> LogicOp.(eval (map go expr))
    in go

  let rec metavars = function
    | MetaVar i -> IntSet.singleton i
    | Op expr -> LogicOp.(collapse IntSet.union (map metavars expr))

  let rec to_string = function
    | MetaVar i -> Printf.sprintf "%d" i
    | Op expr -> LogicOp.to_string (LogicOp.map to_string expr)
end

module type ORDER_STRING = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> String.t
end

module type ORDER_STRING_ARITY = sig
  include ORDER_STRING
  val arity : t -> int
end

module Formula(Var1 : ORDER_STRING)(Var2 : ORDER_STRING_ARITY) = struct
  module Var1Set = Set.Make(Var1)
  module Var2Set = Set.Make(Var2)

  type var1 =
    | Bound of int
    | Free of Var1.t
  [@@deriving ord]

  let free_var_1 = function
    | Bound _ -> Var1Set.empty
    | Free var -> Var1Set.singleton var

  type t =
    | Equal of var1 * var1
    | Member of var1 * var1
    | Forall of t
    | Exists of t
    | Op of t LogicOp.t
  [@@deriving ord]

  let string_of_var_1 depth = function
    | Bound index -> Printf.sprintf "b%d" (depth - 1 - index)
    | Free var -> Printf.sprintf "f%s" (Var1.to_string var)

  let to_string =
    let rec go depth = function
      | Equal (lhs, rhs) -> Printf.sprintf "%s = %s" (string_of_var_1 depth lhs) (string_of_var_1 depth rhs)
      | Member (lhs, rhs) -> Printf.sprintf "%s ∈ %s" (string_of_var_1 depth lhs) (string_of_var_1 depth rhs)
      | Forall inner -> Printf.sprintf "∀%d %s" depth (go (depth + 1) inner)
      | Exists inner -> Printf.sprintf "∃%d %s" depth (go (depth + 1) inner)
      | Op expr -> LogicOp.to_string (LogicOp.map (go depth) expr)
    in go 0

  let rec free_vars_1 = function
    | Equal (x, y) -> Var1Set.union (free_var_1 x) (free_var_1 y)
    | Member (x, y) -> Var1Set.union (free_var_1 x) (free_var_1 y)
    | Forall inner -> free_vars_1 inner
    | Exists inner -> free_vars_1 inner
    | Op expr -> LogicOp.(collapse Var1Set.union (map free_vars_1 expr))

  let has_free_var_1 var formula =
    Var1Set.mem var (free_vars_1 formula)

  let is_closed formula =
    Var1Set.is_empty (free_vars_1 formula)

  let transform_vars_1 f =
    let rec go depth = function
      | Equal (x, y) -> Equal (f depth x, f depth y)
      | Member (x, y) -> Member (f depth x, f depth y)
      | Forall inner -> Forall (go (depth + 1) inner)
      | Exists inner -> Exists (go (depth + 1) inner)
      | Op expr -> Op (LogicOp.map (go depth) expr)
    in go 0

  let bind_1 var =
    transform_vars_1 (fun depth v -> match v with
      | Free x when x = var -> Bound depth
      | _ -> v)

  let substitute_1 var = function
    | Forall inner ->
        let var = Free var in
        transform_vars_1 (fun depth v -> match v with
          | Bound index when index = depth -> var
          | _ -> v) inner
    | _ -> failwith "not a forall"

  let equal x y = Equal(Free x, Free y)
  let member x y = Member(Free x, Free y)
  let forall var inner = Forall(bind_1 var inner)
  let exists var inner = Exists(bind_1 var inner)
  let and_ lhs rhs = Op(And(lhs, rhs))
  let or_ lhs rhs = Op(Or(lhs, rhs))
  let implies lhs rhs = Op(Implies(lhs, rhs))
  let iff lhs rhs = Op(Iff(lhs, rhs))
  let not_ inner = Op(Not inner)
end

module type S = sig
  type var1
  type var2
  type formula
  type judgement    (* an assertion of the form  A1, ... An |- B *)
  type inference    (* a valid propositional calculus logical inference rule *)

  (* natural deduction inference rules *)
  val assumption : formula -> judgement                           (* A |- A *)
  val deduction : formula -> judgement -> judgement               (* from A |- B derive |- A => B *)
  val assuming : formula -> (judgement -> judgement) -> judgement (* |- A => f (... |- A) *)
  val intro_forall : var1 -> judgement -> judgement               (* from |- A derive |- forall x. A *)
  val elim_forall : var1 -> judgement -> judgement                (* from |- forall x. A derive |- A(y) *)
  val intro_exists : var1 -> judgement -> judgement               (* from |- A(y) derive |- exists x. A *)
  val elim_exists : var1 -> formula -> judgement -> judgement     (* from A |- B derive exists x. A |- B *)

  (* sat solver handles logical operators *)
  val inference : Pattern.t list -> Pattern.t -> inference        (* verifies that the conclusion follows *)
  val infer : inference -> judgement list -> formula -> judgement (* apply this inference *)

  val does_prove : judgement -> formula -> bool                   (* whether no assumptions are left *)

  val string_of_formula : formula -> string
  val string_of_judgement : judgement -> string
  val string_of_inference : inference -> string
end

module Make(Var1 : ORDER_STRING)(Var2 : ORDER_STRING_ARITY) : S
with type var1 = Var1.t
and type var2 = Var2.t
and type formula = Formula(Var1)(Var2).t
= struct
  module Formula = Formula(Var1)(Var2)
  module FormulaSet = Set.Make(Formula)

  type var1 = Var1.t
  type var2 = Var2.t
  type formula = Formula.t

  type judgement = {
    context : FormulaSet.t;
    conclusion : formula;
  }

  let assumption formula =
    {
      context = FormulaSet.singleton formula;
      conclusion = formula;
    }

  let deduction formula { context; conclusion } =
    {
      context = FormulaSet.remove formula context;
      conclusion = Formula.implies formula conclusion;
    }

  let assuming formula derivation = deduction formula (derivation (assumption formula))

  let intro_forall var { context; conclusion } =
    if FormulaSet.exists (Formula.has_free_var_1 var) context then failwith "free variable in context";
    { context; conclusion = Formula.forall var conclusion }

  let elim_forall var { context; conclusion } =
    { context ; conclusion = Formula.substitute_1 var conclusion }

  let intro_exists witness { context; conclusion } =
    { context; conclusion = Formula.exists witness conclusion }

  let elim_exists var formula { context ; conclusion } =
    if Formula.has_free_var_1 var conclusion then failwith "free variable in conclusion";
    let context = FormulaSet.remove formula context in
    if FormulaSet.exists (Formula.has_free_var_1 var) context then failwith "free variable in context";
    {
      context = FormulaSet.add (Formula.exists var formula) context;
      conclusion
    }

  type inference = Pattern.t list * Pattern.t

  module IntMap = Map.Make(Int)
  let all_assignments metavars =
    let metavar_inds = IntMap.of_seq (Seq.mapi (fun i var -> (var, i)) (IntSet.to_seq metavars)) in
    Seq.init
      (1 lsl (IntSet.cardinal metavars))
      (fun i var -> (i lsr (IntMap.find var metavar_inds)) land 1 = 1)

  let disproves (premises, conclusion) assignment =
    List.for_all (Pattern.evaluate assignment) premises && not (Pattern.evaluate assignment conclusion)

  let inference premises conclusion =
    let metavars =
      List.fold_left
        (fun acc pattern -> IntSet.union acc (Pattern.metavars pattern))
        (Pattern.metavars conclusion)
        premises in
    if IntSet.cardinal metavars > 20 then failwith "Too complicated, cannot verify";
    let inference = (premises, conclusion) in
    if Seq.exists (disproves inference) (all_assignments metavars) then failwith "Inference is not valid";
    inference

  let rec unify pattern formula assignment =
    match pattern, formula with
    | Pattern.MetaVar i, _ ->
        (match IntMap.find_opt i assignment with
          | Some(formula') -> if formula = formula' then Some assignment else None
          | None -> Some(IntMap.add i formula assignment))
    | Pattern.Op(pexpr), Formula.Op(fexpr) ->
        let kleisli f g x = Option.bind (f x) g in
        Option.bind
          (LogicOp.map2_unify unify pexpr fexpr)
          (fun expr -> LogicOp.collapse kleisli expr assignment)
    | _, _ -> None

  let unify_all =
    List.fold_left2
      (fun assignment pattern formula ->
        Option.bind assignment (unify pattern formula))
      (Some(IntMap.empty))

  let unifies patterns formulas =
    Option.is_some (unify_all patterns formulas)

  let infer (i_premises, i_conclusion) premises conclusion =
    if unifies (List.cons i_conclusion i_premises) (List.cons conclusion (List.map (fun premise -> premise.conclusion) premises))
      then {
        context = List.fold_left (fun context premise -> FormulaSet.union context premise.context) FormulaSet.empty premises;
        conclusion
      }
      else failwith "Inference does not fit pattern"

  let does_prove { context; conclusion } formula =
    FormulaSet.is_empty context
    && Formula.is_closed conclusion
    && conclusion = formula

  let string_of_formula = Formula.to_string
  let string_of_judgement { context; conclusion } =
    Printf.sprintf "%s ⊢ %s"
      (String.concat ", " (List.map string_of_formula (FormulaSet.elements context)))
      (string_of_formula conclusion)
  let string_of_inference (premises, conclusion) =
    Printf.sprintf "%s ⊢ %s"
      (String.concat ", " (List.map Pattern.to_string premises))
      (Pattern.to_string conclusion)
end

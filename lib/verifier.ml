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
    | Implies(lhs, rhs) -> Printf.sprintf "(%s ⇒ %s)" lhs rhs
    | Iff(lhs, rhs) -> Printf.sprintf "(%s ⇔ %s)" lhs rhs
    | And(lhs, rhs) -> Printf.sprintf "(%s ∧ %s)" lhs rhs
    | Or(lhs, rhs) -> Printf.sprintf "(%s ∨ %s)" lhs rhs
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

module Formula(Var : ORDER_STRING) = struct
  type t =
    | Equal of Var.t * Var.t
    | Member of Var.t * Var.t
    | Forall of Var.t * t
    | Exists of Var.t * t
    | Op of t LogicOp.t
  [@@deriving ord]

  let rec to_string = function
    | Equal (lhs, rhs) -> Printf.sprintf "%s = %s" (Var.to_string lhs) (Var.to_string rhs)
    | Member (lhs, rhs) -> Printf.sprintf "%s ∈ %s" (Var.to_string lhs) (Var.to_string rhs)
    | Forall (var, formula) -> Printf.sprintf "∀%s %s" (Var.to_string var) (to_string formula)
    | Exists (var, formula) -> Printf.sprintf "∃%s %s" (Var.to_string var) (to_string formula)
    | Op expr -> LogicOp.to_string (LogicOp.map to_string expr)
end

module type S = sig
  type var
  type formula
  type judgement    (* an assertion of the form  A1, ... An |- B *)
  type inference    (* a valid propositional calculus logical inference rule *)

  (* natural deduction inference rules *)
  val assumption : formula -> judgement                           (* A |- A *)
  val fantasy : formula -> judgement -> judgement                 (* from A |- B derive |- A => B *)
  val assuming : formula -> (judgement -> judgement) -> judgement (* |- A => f (... |- A) *)
  val intro_forall : var -> judgement -> judgement                (* from |- A derive |- forall x. A *)
  val elim_forall : var -> judgement -> judgement                 (* from |- forall x. A derive |- A(y) *)
  val intro_exists : var -> var -> judgement -> judgement         (* from |- A(y) derive |- exists x. A *)
  val elim_exists : var -> formula -> judgement -> judgement      (* from A |- B derive exists x. A |- B *)

  (* sat solver handles logical operators *)
  val inference : Pattern.t list -> Pattern.t -> inference        (* verifies that the conclusion follows *)
  val infer : inference -> judgement list -> formula -> judgement (* apply this inference *)

  val does_prove : judgement -> formula -> bool                   (* whether no assumptions are left *)

  val string_of_formula : formula -> string
  val string_of_judgement : judgement -> string
  val string_of_inference : inference -> string
end

module Make(Var : ORDER_STRING) : S
with type var = Var.t and type formula = Formula(Var).t
= struct
  module VarSet = Set.Make(Var)
  type var = Var.t

  module Formula = struct
    include Formula(Var)

    let rec free_vars : t -> VarSet.t = function
      | Equal (x, y) -> VarSet.of_list [x; y]
      | Member (x, y) -> VarSet.of_list [x; y]
      | Forall (var, formula) -> VarSet.remove var (free_vars formula)
      | Exists (var, formula) -> VarSet.remove var (free_vars formula)
      | Op expr -> LogicOp.(collapse VarSet.union (map free_vars expr))

    let has_free_var v =
      let rec go = function
        | Equal (x, y) -> x = v || y = v
        | Member (x, y) -> x = v || y = v
        | Forall (x, formula) -> x != v && go formula
        | Exists (x, formula) -> x != v && go formula
        | Op expr -> LogicOp.(collapse (fun x y -> x || y) (map go expr))
      in go

    let replace var new_var =
      let replace_var x = if x = var then new_var else x in
      let rec go = function
        | Equal (x, y) -> Equal (replace_var x, replace_var y)
        | Member (x, y) -> Member (replace_var x, replace_var y)
        | Forall (x, formula) -> Forall (x, if x = var then formula else go formula)
        | Exists (x, formula) -> Exists (x, if x = var then formula else go formula)
        | Op expr -> Op (LogicOp.map go expr)
      in go
  end

  type formula = Formula.t

  module FormulaSet = Set.Make(Formula)

  type judgement = {
    context : FormulaSet.t;
    conclusion : formula;
  }

  let assumption formula =
    {
      context = FormulaSet.singleton formula;
      conclusion = formula;
    }

  let fantasy formula { context; conclusion } =
    {
      context = FormulaSet.remove formula context;
      conclusion = Formula.Op(Implies(formula, conclusion));
    }

  let assuming formula deduction = fantasy formula (deduction (assumption formula))

  let intro_forall var { context; conclusion } =
    if FormulaSet.exists (Formula.has_free_var var) context
      then failwith "free variable in context"
      else {
        context;
        conclusion = Forall (var, conclusion);
      }

  let elim_forall var { context; conclusion } =
    match conclusion with
    | Forall(x, formula) -> { context ; conclusion = Formula.replace x var formula }
    | _ -> failwith "not a forall"

  let intro_exists var witness { context; conclusion } =
    {
      context;
      conclusion = Exists (var, Formula.replace witness var conclusion);
    }

  let elim_exists var formula { context ; conclusion } =
    let context = FormulaSet.remove formula context in
    if FormulaSet.exists (Formula.has_free_var var) context
      then failwith "free variable in context"
      else {
        context = FormulaSet.add (Exists(var, formula)) context;
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

  let unifies (patterns : Pattern.t list) (formulas : formula list) =
    Option.is_some (unify_all patterns formulas)

  let infer (i_premises, i_conclusion) premises conclusion =
    if unifies (List.cons i_conclusion i_premises) (List.cons conclusion (List.map (fun premise -> premise.conclusion) premises))
      then {
        context = List.fold_left (fun context premise -> FormulaSet.union context premise.context) FormulaSet.empty premises;
        conclusion
      }
      else failwith "Interence does not fit pattern"

  let does_prove { context; conclusion } formula =
    FormulaSet.is_empty context && VarSet.is_empty (Formula.free_vars conclusion) && conclusion = formula

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

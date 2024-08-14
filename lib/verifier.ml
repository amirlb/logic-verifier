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
  module Var1Map = Map.Make(Var1)
  module Var2Set = Set.Make(Var2)

  type 'a debruijn =
    | Bound of int
    | Free of 'a
  [@@deriving ord]

  let seq_of_debruijn = function
    | Bound _ -> Seq.empty
    | Free x -> Seq.return x

  type var1 = Var1.t debruijn  [@@deriving ord]
  type var2 = Var2.t debruijn  [@@deriving ord]

  type atom =
    | Equal of var1 * var1
    | Member of var1 * var1
    | Apply of var2 * var1 list
  [@@deriving ord]

  type t =
    | Atom of atom
    | Op of t LogicOp.t
    | Forall of t
    | Exists of t
    | Forall2 of int * t
  [@@deriving ord]

  let to_string =
    let db_str to_string depth = function
      | Bound index -> Printf.sprintf "b%d" (depth - 1 - index)
      | Free var -> Printf.sprintf "f%s" (to_string var)
    in let string_of_atom depth = function
      | Equal (lhs, rhs) -> Printf.sprintf "%s = %s" (db_str Var1.to_string depth lhs) (db_str Var1.to_string depth rhs)
      | Member (lhs, rhs) -> Printf.sprintf "%s ∈ %s" (db_str Var1.to_string depth lhs) (db_str Var1.to_string depth rhs)
      | Apply (func, args) -> Printf.sprintf "%s(%s)" (db_str Var2.to_string depth func) (String.concat ", " (List.map (db_str Var1.to_string depth) args))
    in let rec go depth = function
      | Atom atom -> string_of_atom depth atom
      | Op expr -> LogicOp.to_string (LogicOp.map (go depth) expr)
      | Forall inner -> Printf.sprintf "∀%d %s" depth (go (depth + 1) inner)
      | Exists inner -> Printf.sprintf "∃%d %s" depth (go (depth + 1) inner)
      | Forall2 (arity, inner) -> Printf.sprintf "∀%d/%d %s" depth arity (go (depth + 1) inner)
    in go 0

  let free_vars_of_atom = function
    | Equal (x, y) ->
        (Var1Set.of_seq (Seq.append (seq_of_debruijn x) (seq_of_debruijn y)), Var2Set.empty)
    | Member (x, y) ->
        (Var1Set.of_seq (Seq.append (seq_of_debruijn x) (seq_of_debruijn y)), Var2Set.empty)
    | Apply (pred, args) ->
        (Var1Set.of_seq (Seq.concat (Seq.map seq_of_debruijn (List.to_seq args))),
         Var2Set.of_seq (seq_of_debruijn pred))

  let var_sets_union (f11, f21) (f12, f22) =
    (Var1Set.union f11 f12, Var2Set.union f21 f22)

  let rec free_vars = function
    | Atom atom -> free_vars_of_atom atom
    | Op expr -> LogicOp.(collapse var_sets_union (map free_vars expr))
    | Forall inner -> free_vars inner
    | Exists inner -> free_vars inner
    | Forall2 (_, inner) -> free_vars inner

  type parametrized = {
    arguments : Var1.t list;
    template : t;
  }

  let parametrized formula arguments =
    let free_vars_1, free_vars_2 = free_vars formula in
    assert (Var1Set.subset free_vars_1 (Var1Set.of_list arguments));
    assert (Var2Set.is_empty free_vars_2);
    { arguments; template = formula }

  let is_closed formula =
    let free_vars_1, free_vars_2 = free_vars formula in
    Var1Set.is_empty free_vars_1 && Var2Set.is_empty free_vars_2

  let transform_atoms f =
    let rec go depth = function
      | Atom atom -> f depth atom
      | Op expr -> Op (LogicOp.map (go depth) expr)
      | Forall inner -> Forall (go (depth + 1) inner)
      | Exists inner -> Exists (go (depth + 1) inner)
      | Forall2 (arity, inner) -> Forall2 (arity, go (depth + 1) inner)
    in go 0

  let transform_vars_1 f =
    let transform_atom depth = function
      | Equal (x, y) -> Equal (f depth x, f depth y)
      | Member (x, y) -> Member (f depth x, f depth y)
      | Apply (func, args) -> Apply (func, List.map (f depth) args)
    in transform_atoms (fun depth atom -> Atom (transform_atom depth atom))

  let bind_1 var =
    transform_vars_1
      (fun depth v -> match v with Free x when x = var -> Bound depth | _ -> v)

  let bind_2 var =
      transform_atoms
        (fun depth atom -> match atom with
          | Apply (Free x, args) when x = var -> Atom (Apply (Bound depth, args))
          | _ -> Atom atom)

  let substitute_1 var = function
    | Forall inner ->
        let var = Free var in
        let transform_var depth v =
          match v with Bound index when index = depth -> var | _ -> v in
        transform_vars_1 transform_var inner
    | _ -> failwith "not a forall"

  let apply_parametrized_formula {arguments; template} vars =
    if List.length arguments != List.length vars then failwith "wrong number of arguments";
    let subst = Var1Map.of_list (List.combine arguments vars) in
    transform_vars_1 (fun depth v -> match v with
      | Free var ->
        (match Var1Map.find var subst with
          | Free _ as x -> x
          | Bound index -> Bound (depth + index))
      | _ -> v
    ) template

  let substitute_2 f = function
    | Forall2 (arity, inner) ->
        if List.length f.arguments != arity then failwith "wrong number of arguments";
        let transform_atom depth = function
          | Apply (Bound index, args) when index = depth -> apply_parametrized_formula f args
          | _ as atom -> Atom atom
        in transform_atoms transform_atom inner
    | _ -> failwith "not a forall"

  let equal x y = Atom(Equal(Free x, Free y))
  let member x y = Atom(Member(Free x, Free y))
  let apply pred args = Atom(Apply(Free pred, List.map (fun arg -> Free arg) args))
  let and_ lhs rhs = Op(And(lhs, rhs))
  let or_ lhs rhs = Op(Or(lhs, rhs))
  let implies lhs rhs = Op(Implies(lhs, rhs))
  let iff lhs rhs = Op(Iff(lhs, rhs))
  let not_ inner = Op(Not inner)
  let forall var inner = Forall(bind_1 var inner)
  let exists var inner = Exists(bind_1 var inner)
  let forall2 pred inner = Forall2(Var2.arity pred, bind_2 pred inner)
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
  val intro_forall2 : var2 -> judgement -> judgement
  val elim_forall2 : formula -> var1 list -> judgement -> judgement

  (* sat solver handles logical operators *)
  val inference : Pattern.t list -> Pattern.t -> inference        (* verifies that the conclusion follows *)
  val infer : inference -> judgement list -> formula -> judgement (* apply this inference *)

  val premises_of_judgement : judgement -> formula Seq.t
  val conclusion_of_judgement : judgement -> formula
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
  module Var1Set = Set.Make(Var1)
  module Var2Set = Set.Make(Var2)

  type var1 = Var1.t
  type var2 = Var2.t
  type formula = Formula.t

  module Context = struct
    module FormulaMap = Map.Make(Formula)
    type t = (Var1Set.t * Var2Set.t) FormulaMap.t
    let singleton formula = FormulaMap.singleton formula (Formula.free_vars formula)
    let add formula = FormulaMap.add formula (Formula.free_vars formula)
    let remove formula = FormulaMap.remove formula
    let has_free_var_1 var = FormulaMap.exists (fun _ (free1, _) -> Var1Set.mem var free1)
    let has_free_var_2 var = FormulaMap.exists (fun _ (_, free2) -> Var2Set.mem var free2)
    let is_empty = FormulaMap.is_empty
    let premises context = Seq.map fst (FormulaMap.to_seq context)
    let union = FormulaMap.union (fun _ x _ -> Some(x))
    let union_all = List.fold_left union FormulaMap.empty
  end

  type judgement = {
    context : Context.t;
    conclusion : formula;
  }

  let assumption formula =
    {
      context = Context.singleton formula;
      conclusion = formula;
    }

  let deduction formula { context; conclusion } =
    {
      context = Context.remove formula context;
      conclusion = Formula.implies formula conclusion;
    }

  let assuming formula derivation = deduction formula (derivation (assumption formula))

  let intro_forall var { context; conclusion } =
    if Context.has_free_var_1 var context then failwith "free variable in context";
    { context; conclusion = Formula.forall var conclusion }

  let elim_forall var { context; conclusion } =
    { context ; conclusion = Formula.substitute_1 var conclusion }

  let intro_exists witness { context; conclusion } =
    { context; conclusion = Formula.exists witness conclusion }

  let elim_exists var formula { context ; conclusion } =
    if Var1Set.mem var (fst (Formula.free_vars conclusion)) then failwith "free variable in conclusion";
    let context = Context.remove formula context in
    if Context.has_free_var_1 var context then failwith "free variable in context";
    {
      context = Context.add (Formula.exists var formula) context;
      conclusion
    }

  let intro_forall2 var { context; conclusion } =
    if Context.has_free_var_2 var context then failwith "free variable in context";
    { context; conclusion = Formula.forall2 var conclusion }

  let elim_forall2 formula arguments { context; conclusion } =
    let f = Formula.parametrized formula arguments in
    { context ; conclusion = Formula.substitute_2 f conclusion }

  module PatternRules = struct
    type t = Pattern.t list * Pattern.t

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

    let unifies inference formula_nodes =
      Option.is_some (
        List.fold_left2
          (fun assignment pattern formula_node -> Option.bind assignment (unify pattern formula_node))
          (unify (snd inference) (snd formula_nodes) IntMap.empty)
          (fst inference)
          (fst formula_nodes))
  end

  type inference = PatternRules.t

  let inference = PatternRules.inference

  let infer inference premises conclusion =
    let formula_nodes = (List.map (fun premise -> premise.conclusion) premises, conclusion) in
    if not (PatternRules.unifies inference formula_nodes) then failwith "Inference does not fit pattern";
    {
      context = Context.union_all (List.map (fun premise -> premise.context) premises);
      conclusion
    }

  let premises_of_judgement judgement = Context.premises judgement.context
  let conclusion_of_judgement judgement = judgement.conclusion

  let does_prove { context; conclusion } formula =
    Context.is_empty context
    && Formula.is_closed conclusion
    && conclusion = formula

  let string_of_formula = Formula.to_string
  let string_of_judgement { context; conclusion } =
    Printf.sprintf "%s ⊢ %s"
      (String.concat ", " (List.of_seq (Seq.map string_of_formula (Context.premises context))))
      (string_of_formula conclusion)
  let string_of_inference (premises, conclusion) =
    Printf.sprintf "%s ⊢ %s"
      (String.concat ", " (List.map Pattern.to_string premises))
      (Pattern.to_string conclusion)
end

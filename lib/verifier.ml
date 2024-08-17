module type OrderedPrintable = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
end

module LogicOp = struct
  type 'a t =
    | And of 'a * 'a
    | Or of 'a * 'a
    | Implies of 'a * 'a
    | Iff of 'a * 'a
    | Not of 'a
  [@@deriving ord, map]

  let to_string = function
    | And(lhs, rhs) -> Printf.sprintf "(%s ∧ %s)" lhs rhs
    | Or(lhs, rhs) -> Printf.sprintf "(%s ∨ %s)" lhs rhs
    | Implies(lhs, rhs) -> Printf.sprintf "(%s ⇒ %s)" lhs rhs
    | Iff(lhs, rhs) -> Printf.sprintf "(%s ⇔ %s)" lhs rhs
    | Not(inner) -> Printf.sprintf "¬%s" inner

  let eval = function
    | And(lhs, rhs) -> lhs && rhs
    | Or(lhs, rhs) -> lhs || rhs
    | Implies(lhs, rhs) -> not lhs || rhs
    | Iff(lhs, rhs) -> lhs = rhs
    | Not(value) -> not value

  let collapse f = function
    | And(lhs, rhs) -> f lhs rhs
    | Or(lhs, rhs) -> f lhs rhs
    | Implies(lhs, rhs) -> f lhs rhs
    | Iff(lhs, rhs) -> f lhs rhs
    | Not(value) -> value

  let map2_unify f c1 c2 = match c1, c2 with
    | And(lhs1, rhs1), And(lhs2, rhs2) -> Some(And(f lhs1 lhs2, f rhs1 rhs2))
    | Or(lhs1, rhs1), Or(lhs2, rhs2) -> Some(Or(f lhs1 lhs2, f rhs1 rhs2))
    | Implies(lhs1, rhs1), Implies(lhs2, rhs2) -> Some(Implies(f lhs1 lhs2, f rhs1 rhs2))
    | Iff(lhs1, rhs1), Iff(lhs2, rhs2) -> Some(Iff(f lhs1 lhs2, f rhs1 rhs2))
    | Not(inner1), Not(inner2) -> Some(Not(f inner1 inner2))
    | _ -> None
end

module IntMap = Map.Make(Int)

module Pattern = struct
  type t =
    | MetaVar of int
    | Op of t LogicOp.t
  [@@deriving ord]

  let metavar n = MetaVar n
  let and_ lhs rhs = Op (And (lhs, rhs))
  let or_ lhs rhs = Op (Or (lhs, rhs))
  let implies lhs rhs = Op (Implies (lhs, rhs))
  let iff lhs rhs = Op (Iff (lhs, rhs))
  let not_ inner = Op (Not inner)

  type inference = t list * t

  let rec to_string = function
    | MetaVar i -> Printf.sprintf "%d" i
    | Op expr -> LogicOp.to_string (LogicOp.map to_string expr)

  module IntSet = Set.Make(Int)

  let rec evaluate assignment = function
    | MetaVar i -> assignment i
    | Op expr -> LogicOp.(eval (map (evaluate assignment) expr))

  let rec metavars = function
    | MetaVar i -> IntSet.singleton i
    | Op expr -> LogicOp.(collapse IntSet.union (map metavars expr))

  let all_assignments metavars =
    let metavar_inds = IntMap.of_seq (Seq.mapi (fun i var -> (var, i)) (IntSet.to_seq metavars)) in
    Seq.init
      (1 lsl (IntSet.cardinal metavars))
      (fun i var -> (i lsr (IntMap.find var metavar_inds)) land 1 = 1)

  let disproves (premises, conclusion) assignment =
    List.for_all (evaluate assignment) premises && not (evaluate assignment conclusion)

  let consequence premises conclusion =
    let metavars =
      List.fold_left
        (fun acc pattern -> IntSet.union acc (metavars pattern))
        (metavars conclusion)
        premises in
    if IntSet.cardinal metavars > 20 then failwith "Too complicated, cannot verify";
    let inference = (premises, conclusion) in
    if Seq.exists (disproves inference) (all_assignments metavars) then failwith "Inference is not valid";
    inference
end

module Var1 = struct
  type t = int
  [@@deriving ord]

  let gen =
    let ctr = ref 0
    in fun () -> ctr := !ctr + 1; !ctr

  let to_string n = Printf.sprintf "x%d" n
end

type arity = int
[@@deriving ord]

module Var2 = struct
  type t = Builtin of arity * string | Auto of arity * int
  [@@deriving ord]

  let get_arity = function
    | Builtin (arity, _) -> arity
    | Auto (arity, _) -> arity

  let gen =
    let ctr = ref 0
    in fun arity -> ctr := !ctr + 1; Auto (arity, !ctr)

  let to_string = function
    | Builtin (arity, name) -> Printf.sprintf "%s/%d" name arity
    | Auto (arity, n) -> Printf.sprintf "p%d/%d" n arity
end

let make_builtin arity name = Var2.Builtin (arity, name)

module Var1Set = Set.Make(Var1)
module Var2Set = Set.Make(Var2)

module BaseFormula = struct
  type 'a debruijn = Bound of int | Free of 'a
  [@@deriving ord]

  type ('var1, 'var2) t =
    | Apply of 'var2 debruijn * 'var1 debruijn list
    | Op of ('var1, 'var2) t LogicOp.t
    | Forall of ('var1, 'var2) t
    | Exists of ('var1, 'var2) t
    | Forall2 of arity * ('var1, 'var2) t
  [@@deriving ord]

  let rec map_aux f depth = function
    | Apply (pred, args) -> f depth pred args
    | Op expr -> Op (LogicOp.map (map_aux f depth) expr)
    | Forall inner -> Forall (map_aux f (depth + 1) inner)
    | Exists inner -> Exists (map_aux f (depth + 1) inner)
    | Forall2 (arity, inner) -> Forall2 (arity, map_aux f (depth + 1) inner)

  let map f = map_aux f 0

  let map_var1 f =
    map (fun depth pred args -> Apply (pred, List.map (f depth) args))
end

module Formula = struct
  open BaseFormula

  type t = (Var1.t, Var2.t) BaseFormula.t
  [@@deriving ord]

  let apply pred args =
    assert (Var2.get_arity pred = List.length args);
    Apply (Free pred, List.map (fun var -> Free var) args)
  let and_ lhs rhs = Op (And (lhs, rhs))
  let or_ lhs rhs = Op (Or (lhs, rhs))
  let implies lhs rhs = Op (Implies (lhs, rhs))
  let iff lhs rhs = Op (Iff (lhs, rhs))
  let not_ inner = Op (Not inner)

  let bind var =
    BaseFormula.map_var1 (fun depth -> function Free x when x = var -> Bound depth | v -> v)

  let bind_pred var =
    let transform_pred depth = function Free p when p = var -> Bound depth | pred -> pred
    in BaseFormula.map (fun depth pred args -> Apply (transform_pred depth pred, args))

  let forall f = let x = Var1.gen () in Forall (bind x (f x))
  let exists f = let x = Var1.gen () in Exists (bind x (f x))
  let forall2 arity f = let p = Var2.gen arity in Forall2 (arity, bind_pred p (f p))

  (* TODO: nicer print: normalize variable names, take hints from user *)
  let db_str to_string depth = function
    | Bound index -> Printf.sprintf "%d" (depth - 1 - index)
    | Free var -> to_string var
  let rec to_string_aux depth = function
    | Apply (pred, args) ->
        Printf.sprintf "%s(%s)" (db_str Var2.to_string depth pred) (String.concat ", " (List.map (db_str Var1.to_string depth) args))
    | Op expr -> LogicOp.to_string (LogicOp.map (to_string_aux depth) expr)
    | Forall inner -> Printf.sprintf "∀%d %s" depth (to_string_aux (depth + 1) inner)
    | Exists inner -> Printf.sprintf "∃%d %s" depth (to_string_aux (depth + 1) inner)
    | Forall2 (arity, inner) -> Printf.sprintf "∀%d/%d %s" depth arity (to_string_aux (depth + 1) inner)
  let to_string = to_string_aux 0

  let substitute var =
    BaseFormula.map_var1 (fun depth -> function Bound index when index = depth -> Free var | v -> v)

  let free_vars_union (f11, f21) (f12, f22) = (Var1Set.union f11 f12, Var2Set.union f21 f22)
  let build_free_vars1 vars =
    Var1Set.of_list (List.filter_map (function Free x -> Some x | Bound _ -> None) vars)
  let build_free_vars2 = function
    | Free x -> Var2Set.singleton x
    | Bound _ -> Var2Set.empty
  let rec free_vars = function
    | Apply (pred, args) -> (build_free_vars1 args, build_free_vars2 pred)
    | Op expr -> LogicOp.(collapse free_vars_union (map free_vars expr))
    | Forall inner -> free_vars inner
    | Exists inner -> free_vars inner
    | Forall2 (_, inner) -> free_vars inner
end

module Predicate = struct
  open BaseFormula

  type var1 = Parameter of int | Var of Var1.t
  [@@deriving ord]

  type template = (var1, Var2.t) BaseFormula.t
  [@@deriving ord]

  type t = arity * template
  [@@deriving ord]

  let from_var var =
    let arity = Var2.get_arity var in
    let template = Apply (Free var, List.init arity (fun i -> Free (Parameter i))) in
    (arity, template)

  module Var1Map = Map.Make(Var1)

  let build_template param_inds =
    let transform_var depth : Var1.t debruijn -> var1 debruijn = function
      | Bound index -> assert (index <= depth); Bound index
      | Free var -> match Var1Map.find_opt var param_inds with
          | None -> Free (Var var)
          | Some ind -> Free (Parameter ind)
    in let validate_pred depth = function
      | Bound index -> assert (index <= depth)
      | _ -> ()
    in let aux depth pred args =
      validate_pred depth pred;
      Apply (pred, List.map (transform_var depth) args)
    in BaseFormula.map aux

  let from_formula arity f =
    let args = List.init arity (fun _ -> Var1.gen ()) in
    let param_inds = Var1Map.of_list (List.mapi (fun i arg -> (arg, i)) args) in
    (arity, build_template param_inds (f args))

  let get_arity (arity, _) = arity

  let apply_template (arity, template) params =
    let transform_var depth = function
      | Bound index -> assert (index <= depth); Bound index
      | Free (Var var) -> Free var
      | Free (Parameter i) -> match List.nth params i with
        | Bound index -> Bound (depth + index)
        | var -> var in
    assert (List.length params = arity);
    BaseFormula.map_var1 transform_var template

  let substitute template =
    let transform_atom depth pred args = match pred with
      | Bound index when index = depth -> apply_template template args
      | _ -> Apply (pred, args)
    in BaseFormula.map transform_atom

  let to_string _ = "TODO"
end

module Context = struct
  module FormulaMap = Map.Make(Formula)
  type t = (Var1Set.t * Var2Set.t) FormulaMap.t
  let singleton formula = FormulaMap.singleton formula (Formula.free_vars formula)
  let add formula = FormulaMap.add formula (Formula.free_vars formula)
  let remove formula = FormulaMap.remove formula
  let has_free_var1 var = FormulaMap.exists (fun _ (free1, _) -> Var1Set.mem var free1)
  let has_free_var2 var = FormulaMap.exists (fun _ (_, free2) -> Var2Set.mem var free2)
  let premises context = Seq.map fst (FormulaMap.to_seq context)
  let union = FormulaMap.union (fun _ x _ -> Some(x))
  let union_all = List.fold_left union FormulaMap.empty
end

module Verifier = struct
  type t = {
    context : Context.t;
    conclusion : Formula.t;
  }

  let premises judgement = Context.premises judgement.context
  let conclusion judgement = judgement.conclusion

  let to_string judgement =
    Printf.sprintf "%s ⊢ %s"
      (String.concat ", " (List.of_seq (Seq.map Formula.to_string (Context.premises judgement.context))))
      (Formula.to_string judgement.conclusion)

  let assuming formula derivation =
    let assumption = { context = Context.singleton formula; conclusion = formula } in
    let { context; conclusion } = derivation assumption
    in {
      context = Context.remove formula context;
      conclusion = Formula.implies formula conclusion;
    }
  
  let rec unify pattern formula assignment =
    match pattern, formula with
    | Pattern.MetaVar i, _ ->
        (match IntMap.find_opt i assignment with
          | Some(formula') -> if formula = formula' then Some assignment else None
          | None -> Some(IntMap.add i formula assignment))
    | Pattern.Op(pexpr), BaseFormula.Op(fexpr) ->
        let kleisli f g x = Option.bind (f x) g in
        Option.bind
          (LogicOp.map2_unify unify pexpr fexpr)
          (fun expr -> LogicOp.collapse kleisli expr assignment)
    | _, _ -> None

  let unifies (inference_premises, inference_conclusion) premises conclusion =
    Option.is_some (
      List.fold_left2
        (fun assignment pattern formula_node -> Option.bind assignment (unify pattern formula_node))
        (unify inference_conclusion conclusion IntMap.empty)
        inference_premises
        premises)

  let infer inference premises conclusion =
    let premise_formulas = List.map (fun judgement -> judgement.conclusion) premises in
    if not (unifies inference premise_formulas conclusion) then failwith "Inference does not fit pattern";
    {
      context = Context.union_all (List.map (fun judgement -> judgement.context) premises);
      conclusion
    }

  let intro_forall f =
    let var = Var1.gen () in
    let { context; conclusion } = f var in
    if Context.has_free_var1 var context then failwith "free variable in context";
    { context; conclusion = Formula.(Forall (bind var conclusion)) }

  let elim_forall var judgement =
    match judgement.conclusion with
      | Forall inner -> { judgement with conclusion = Formula.substitute var inner }
      | _ -> failwith "not a forall"

  let intro_exists var judgement =
    { judgement with conclusion = Formula.(Exists (bind var judgement.conclusion)) }

  let elim_exists var formula judgement =
    let free_in_conclusion, _ = Formula.free_vars judgement.conclusion in
    if Var1Set.mem var free_in_conclusion then failwith "free variable in conclusion";
    let context = Context.remove formula judgement.context in
    if Context.has_free_var1 var context then failwith "free variable in context";
    { judgement with context = Context.add (Formula.(Exists (bind var formula))) context }

  let intro_forall2 arity f =
    let var = Var2.gen arity in
    let { context; conclusion } = f var in
    if Context.has_free_var2 var context then failwith "free variable in context";
    { context; conclusion = Formula.(Forall2 (arity, bind_pred var conclusion)) }

  let elim_forall2 pred judgement =
    match judgement.conclusion with
    | Forall2 (arity, inner) ->
        if arity != Predicate.get_arity pred then failwith "wrong arity";
        { judgement with conclusion = Predicate.substitute pred inner }
    | _ -> failwith "not a forall"
end

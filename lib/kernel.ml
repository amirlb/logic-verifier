module Proposition = struct
  module Base = struct
    module MVar = String

    (* TODO: constrain argument list with GADTs *)
    type 'a sym =
      | Not
      | And
      | Or
      | Implies
      | User of 'a
                  [@@deriving map, ord]

    type 'a t =
      | Metavar of MVar.t
      | Fun of 'a sym * 'a t list
                          [@@deriving map, ord]

    let mk_not p = Fun(Not, [p])
    let mk_or l r = Fun(Or, [l; r])
    let mk_and l r = Fun(And, [l; r])
    let mk_implies l r = Fun(Implies, [l; r])
    let mk_fun s args = Fun(User s, args)
    let mk_meta s = Metavar(s)

  end
  include Base

  let rec to_string f t = match t with
    | Fun(User s, []) ->  f s
    | Metavar s -> Printf.sprintf "?%s" s
    | Fun(Not, [p]) -> Printf.sprintf "¬%s" (to_string f p)
    | Fun(And, [p; q]) -> Printf.sprintf "(%s ∧ %s)" (to_string f p) (to_string f q)
    | Fun(Or,  [p; q])     -> Printf.sprintf "(%s ∨ %s)" (to_string f p) (to_string f q)
    | Fun(Implies, [p; q]) -> Printf.sprintf "(%s → %s)" (to_string f p) (to_string f q)
    | Fun(User nm, args) ->  Printf.sprintf "%s(%s)" (f nm) (String.concat ", " (List.map (to_string f) args))
    | Fun(Not, _)
    | Fun(And, _)
    | Fun(Or, _)
    | Fun(Implies, _) -> failwith "Invalid ctor" (* FIXME: GADTs to the rescue? *)

  module Infix = struct
    let ( ~= ) atom = mk_fun atom []
    let ( ~? ) nm = mk_meta nm
    let ( ~! ) p = mk_not p
    let ( @-> ) l r = mk_implies l r
    let ( <&> ) l r = mk_and l r
    let ( <|> ) l r = mk_or l r
  end
end

module type ORDER_STRING = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> String.t
end

module type S = sig
  type name
  type prop = name Proposition.t
  type t                        (* judgement *)

  (* Some helper functions *)
  val canonical : prop -> int Proposition.t * name list

  type unification_error =
    | Occurs of Proposition.MVar.t * prop
    | Conflict of prop * prop
  val unify : prop -> prop -> ((Proposition.MVar.t * prop) list, unification_error) result

  type rule
  val ( |~> ) : prop -> prop -> rule
  val rule : rule list -> (t -> t)

  val join : t -> t -> t
  val separate : t -> t * t
  val add_doubleneg : t -> t
  val rem_doubleneg : t -> t
  val assume : prop -> t
  val fantasy : prop -> t -> t
  val detachment : t -> t -> t
  val contrapositive1 : t -> t
  val contrapositive2 : t -> t
  val de_morgan : t -> t
  val switcheroo : t -> t
  val proof : t -> prop
end

module Make(A : ORDER_STRING) : S with type name := A.t = struct
  type prop = A.t Proposition.t
  let to_string p = Proposition.to_string A.to_string p
  let compare p p' = Proposition.compare A.compare p p'

  module PropOrder = struct
    type t = prop
    let compare = compare
  end

  module SMap = Map.Make(Proposition.MVar)
  module Context = Set.Make(PropOrder)
  type t = Judgement of Context.t * prop

  let canonical p =
    let module AMap = Map.Make(A) in
    let uniq = ref AMap.empty
    and perm = ref []
    and last = ref 0 in
    let aux a = match AMap.find_opt a !uniq with
      | Some i -> i
      | None -> let i = !last in
                begin
                  uniq := AMap.add a i !uniq;
                  perm := a :: !perm;
                  incr last;
                  i
                end
    in
    let t' = Proposition.map aux p in
    t', (List.rev !perm)

  let occurs s t =
    let rec aux : prop -> bool = function
      | Metavar s' -> Proposition.MVar.equal s s'
      | Fun(_, ts) -> List.exists aux ts
    in
    aux t

  type unification_error =
    | Occurs of Proposition.MVar.t * prop
    | Conflict of prop * prop

  exception Done of unification_error

    let apply_subst subst t =
      let rec aux = function
      | (Proposition.Metavar v) as t -> (match SMap.find_opt v subst with
                             | None -> t, false
                             | Some t' -> t', true)
      | Fun(f, args) as t ->
         let isnew, args' = List.fold_left (fun (isnew, args) a ->
                                let a', anew = aux a in
                                isnew || anew, a'::args)
                              (false, [])
                              args
         in
         (if isnew then Fun(f, List.rev args') else t), isnew
      in
      fst (aux t)

  let unify l r =
    let env = ref SMap.empty in
    let add_subst v t =
      env := SMap.update v (function
                 | None -> Some (ref t)
                 | (Some r) as aref -> r := t; aref)
               !env
    in

    (* Substitution with path compression *)
    let drill t =
      let rec aux : prop -> prop = function
        | Fun(_, _) as t -> t
        | (Metavar v) as t -> match SMap.find_opt v !env with
                              | None -> t
                              | Some t' -> let final = aux !t' in
                                           add_subst v final;
                                           final
      in
      aux t

    in
    let rec aux l r =
      let l, r = (drill l), (drill r) in
      match l, r with
      | Fun(fl, largs), Fun(fr, rargs) ->
         if 0 = Proposition.compare_sym A.compare fl fr then
           try List.iter2 aux largs rargs with
           | Invalid_argument _ -> raise (Done(Conflict(l, r)))
         else
           raise (Done(Conflict(l, r)))
      | Fun(_, _) as t, Metavar v | Metavar v, (Fun(_, _) as t) ->
         (* occurs check is in a later stage *)
         add_subst v t
      | Metavar vl, Metavar vr ->
         match Proposition.MVar.compare vl vr with
         | 0 -> ()
         (* Avoid cycles: orient substitutions in the direction of the "smaller" var *)
         | t when t < 0 ->
            add_subst vr l
         | _ ->
            add_subst vl r
    in

    try begin
        aux l r;
        (* Normalize substitutions *)
        let final = SMap.fold
                      (fun v t state -> let t' = apply_subst state !t in
                                        if occurs v t' then
                                          raise (Done(Occurs(v, t')))
                                        else
                                          SMap.add v t' state)
                      !env
                      SMap.empty
        in
        final |> SMap.to_seq |> List.of_seq |> Result.ok
      end
    with
    | Done(e) -> Result.error e

  let correct ctx p =
    let ctx_str = String.concat ", " (List.map to_string (Context.elements ctx)) in
    Printf.printf "%s ⊢ %s\n" ctx_str (to_string p);
    Judgement (ctx, p)

  let inference f (Judgement (ctx, p)) = correct ctx (f p)

  exception Rule_fail of prop list

  type rule = Rule of {lhs: prop; rhs: prop}

  let ( |~> ) lhs rhs = Rule {lhs; rhs}

  let rewrite (Rule{lhs; rhs}) p =
    match unify lhs p with
    | Ok subst ->
       let final = apply_subst (subst |> List.to_seq |> SMap.of_seq) rhs
       in
       Result.ok final
    | Error _ ->
       Result.error [lhs]

  let rule cs =
    let helper p =
      let ok, fail = List.partition_map (fun r -> rewrite r p
                                                  |> Result.fold
                                                       ~ok:Either.left
                                                       ~error:Either.right)
                       cs
      in
      match ok with
      | [] -> raise (Rule_fail (List.concat fail))
      | c :: _ -> c
  in
  inference helper

  let join (Judgement (ctx1, p1)) (Judgement (ctx2, p2)) =
    correct (Context.union ctx1 ctx2) (Proposition.mk_and p1 p2)

  let separate (Judgement (ctx, p)) = match p with
    | Fun(And, [p1; p2]) -> correct ctx p1, correct ctx p2
    | _ -> failwith "Not an And proposition"

  let assume p = correct (Context.singleton p) p

  let fantasy p (Judgement (ctx, q)) =
    correct (Context.remove p ctx) (Fun(Implies, [p; q]))

  let detachment (Judgement (ctx1, p)) (Judgement (ctx2, q)) = match q with
    | Fun(Implies, [p1; p2]) when compare p1 p = 0 ->
        correct (Context.union ctx1 ctx2) p2
    | _ -> failwith ("Not a detachment (" ^ to_string p ^ ", " ^ to_string q ^ ")")

  let proof (Judgement (ctx, p)) =
    if Context.is_empty ctx
      then p
    else failwith "Context is not empty"

  open Proposition.Infix

  let p = ~?"P"
  let q = ~?"Q"

  let add_doubleneg = rule [p |~> ~! ~! p]
  let rem_doubleneg = rule [~! ~! p |~> p]

  let contrapositive1 = rule [p @-> q |~> ~!q @-> ~!p]

  let contrapositive2 = rule [~!q @-> ~!p |~> p @-> q]

  let de_morgan = rule [
                     (~!p <&> ~!q) |~> ~!(p <|> q);
                     (~!p <|> ~!q) |~> ~!(p <&> q);
                    ]
  let switcheroo = rule [
                       (~!p @-> q) |~> (p <|> q);
                       (p <|> q) |~> (~!p @-> q);
                     ]
end

module String = Make(struct include String let to_string t = t end)

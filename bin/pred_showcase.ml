module P = Logic.Verifier.Pattern

module Name = struct
  type t = string
  let compare = String.compare
  let to_string x = x
end

module Name2 = struct
  type t = (string * int)
  let compare = Stdlib.compare
  let to_string (name, arity) = Printf.sprintf "%s/%d" name arity
  let arity (_, arity) = arity
end

module V = Logic.Verifier.Make(Name)(Name2)

module F = Logic.Verifier.Formula(Name)(Name2)

let example_1 =
  let x_eq_x = F.equal "x" "x" in
  let p_imp_p = F.implies x_eq_x x_eq_x in
  let gen_p_imp_p = F.forall "x" p_imp_p in
  let proof = V.(intro_forall "x" (assuming x_eq_x (fun p -> p))) in
  (gen_p_imp_p, proof)

let example_2 =
  let subset a b = F.(forall "x" (implies (member "x" a) (member "x" b))) in
  let a_ss_b_ss_c = F.(and_ (subset "a" "b") (subset "b" "c")) in
  let claim = F.(forall "a" (forall "b" (forall "c" (implies a_ss_b_ss_c  (subset "a" "c"))))) in

  let conj_1 = V.inference [Op(And(MetaVar 1, MetaVar 2))] (MetaVar 1) in
  let conj_2 = V.inference [Op(And(MetaVar 1, MetaVar 2))] (MetaVar 2) in
  let m_p = V.inference [Op(Implies(MetaVar 1, MetaVar 2)); MetaVar 1] (MetaVar 2) in
  let proof = V.(intro_forall "a" (intro_forall "b" (intro_forall "c" (assuming a_ss_b_ss_c (fun p ->
    let a_ss_b = infer conj_1 [p] (subset "a" "b") in
    let b_ss_c = infer conj_2 [p] (subset "b" "c") in
    let a_ss_c = assuming F.(member "x" "a") (fun x_in_a -> 
      let x_in_b = infer m_p [elim_forall "x" a_ss_b; x_in_a] F.(member "x" "b") in
      let x_in_c = infer m_p [elim_forall "x" b_ss_c; x_in_b] F.(member "x" "c") in
      x_in_c
    ) in
    intro_forall "x" a_ss_c
  ))))) in

  (claim, proof)

let example_3 =
  let tautology = F.(or_ (member "x" "y") (not_ (member "x" "y"))) in
  let claim = F.(forall "x" (forall "y" tautology)) in

  let p_or_not_p = V.inference [] P.(Op(Or(MetaVar 0, Op(Not(MetaVar 0))))) in
  let proof = V.(intro_forall "x" (intro_forall "y" (infer p_or_not_p [] tautology))) in

  (claim, proof)

(* TODO: implement second-order logic *)
(* let example_4 =
  let axiom = F.(Forall2("P", Forall("x", Forall("y",
    Op(Implies(Equal("x", "y"), Op(Iff(Apply("P", ["x"]), Apply("P", ["y"]))))))))) in
  let property a = F.(Forall("x", Member("x", a))) in
  let claim = F.(Forall("a", Forall("b",
    Op(Implies(Op(And(axiom, Op(And(property "a", Equal("a", "b"))))),
               property "b"))))) in

  let proof = () in

  (claim, proof) *)

let validate (claim, proof) =
  assert (V.does_prove proof claim);
  Printf.printf "Verified: %s\n" (V.string_of_formula claim)

let main () =
  validate example_1;
  validate example_2;
  validate example_3;

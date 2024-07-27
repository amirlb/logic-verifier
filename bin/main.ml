module Proposition = Logic.Kernel.Proposition
module Kernel = Logic.Kernel.String

let print_position outx lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_string s =
  let lexbuf = Lexing.from_string ~with_positions:true s in
  try Logic.Parser.proof Logic.Lexer.main lexbuf with
  | Logic.Parser.Error ->
     Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
     exit (-1)

let proof1 =
  let final = parse_string "assume P
                            add_doubleneg _
                            fantasy P _
                            "
  in Kernel.proof final

let proof2 =
  let final = parse_string "PandQ = P & Q
                            assume _
                            dp, dq = separate _
                            join dq, dp
                            fantasy PandQ _
                            "
  in Kernel.proof final

let proof3 =
  let final = parse_string "p = assume P
                            q = assume Q
                            join p, q
                            fantasy Q _
                            fantasy P _
                            "
  in
  Kernel.proof final

let gantos_ax =
  let final = parse_string "Axiom = (P -> Q) & (~P -> Q)
                            assume Axiom
                            p_imp_q, not_p_imp_q = separate _
                            assume ~P
                            fantasy ~P _
                            p_or_not_p = switcheroo _

                            nq = assume ~Q
                            lol = contrapositive1 p_imp_q
                            j1 = detachment nq, _
                            contrapositive1 not_p_imp_q
                            j2 = detachment nq, _

                            join j1, j2
                            de_morgan _
                            fantasy ~Q _
                            contrapositive2 _
                            detachment p_or_not_p, _
                            fantasy Axiom _
                            "
  in Kernel.proof final

let by_contradiction =
  let final = parse_string "PnP = P & ~P
                            assume _
                            NQ = ~Q
                            dp, dnp = separate _
                            add_doubleneg dp
                            fantasy NQ _
                            contrapositive2 _
                            detachment dnp, _
                            fantasy PnP _
                            "
  in
  Kernel.proof final

let () =
  let to_string p = Proposition.to_string (fun t -> t) p
  in

  print_endline "Results";
  print_endline (to_string proof1);

  print_endline (to_string proof2);
  print_endline (to_string proof3);
  print_endline (to_string gantos_ax);
  print_endline (to_string by_contradiction);


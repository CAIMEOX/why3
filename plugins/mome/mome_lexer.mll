(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{
  open Lexing
  open Why3
  open Mome_parser

  let keywords = Hashtbl.create 97

  let () = List.iter (fun (x,y) -> Hashtbl.add keywords x y)
    [ "let",      LET;
      "endlet",   ENDLET;
      "fun",      FUN;
      "endfun",   ENDFUN;
      "rec",      REC;
      "endrec",   ENDREC;
      "in",       IN;
      "endin",    ENDIN;
      "if",       IF;
      "then",     THEN;
      "else",     ELSE;
      "endif",    ENDIF;
      "while",    WHILE;
      "do",       DO;
      "done",     DONE;
      "with",     WITH;
      "endwith",  ENDWITH;
      "where",    WHERE;
      "endwhere", ENDWHERE;
(*
      "break",    BREAK;
      "continue", CONTINUE;
      "return",   RETURN;
*)
      "true",     TRUE;
      "false",    FALSE;
      "as",       AS;
      "and",      AND;
    ]

  type lang = {
    is_opener: (token, unit) Hashtbl.t;
    (* open group *)
    is_lax: (token, unit) Hashtbl.t;
    implicit_sep: (token, token) Hashtbl.t;
    implicit_end: (token, token) Hashtbl.t;
    (* separator and closer group *)
    is_sep_end: (token, unit) Hashtbl.t;
    is_sep_for: (token * token, unit) Hashtbl.t;
    is_end_for: (token * token, unit) Hashtbl.t;
    (* fragile tokens *)
    is_fragile: (token, unit) Hashtbl.t;
  }

  let is_opener l t = Hashtbl.mem l.is_opener t
  let is_lax l t = Hashtbl.mem l.is_lax t
  let implicit_sep l t = Hashtbl.find_opt l.implicit_sep t
  let implicit_end l t = Hashtbl.find_opt l.implicit_end t
  let is_sep_end l t = Hashtbl.mem l.is_sep_end t
  let is_sep_for l t s = Hashtbl.mem l.is_sep_for (t,s)
  let is_end_for l t s = Hashtbl.mem l.is_end_for (t,s)
  let is_fragile l t = Hashtbl.mem l.is_fragile t

  let declare_box lang ?(lax = false)
        ?isep ?(seps = []) ?iend ?(ends = []) t =
    Hashtbl.replace lang.is_opener t ();
    if lax then Hashtbl.replace lang.is_lax t ()
           else Hashtbl.remove  lang.is_lax t;
    ( match isep with
      | Some s -> Hashtbl.replace lang.is_sep_end s ();
                  Hashtbl.replace lang.is_sep_for (s,t) ();
                  Hashtbl.replace lang.implicit_sep t s
      | None   -> Hashtbl.remove  lang.implicit_sep t );
    ( match iend with
      | Some s -> Hashtbl.replace lang.is_sep_end s ();
                  Hashtbl.replace lang.is_end_for (s,t) ();
                  Hashtbl.replace lang.implicit_end t s;
      | None   -> Hashtbl.remove  lang.implicit_end t );
    List.iter (fun s -> Hashtbl.replace lang.is_sep_end s ();
                        Hashtbl.replace lang.is_sep_for (s,t) ()) seps;
    List.iter (fun s -> Hashtbl.replace lang.is_sep_end s ();
                        Hashtbl.replace lang.is_end_for (s,t) ()) ends

  let declare_fragile lang s =
    Hashtbl.replace lang.is_fragile s ()

  let lang = {
    is_opener = Hashtbl.create 3;
    is_lax = Hashtbl.create 3;
    implicit_sep = Hashtbl.create 3;
    implicit_end = Hashtbl.create 3;
    is_sep_end = Hashtbl.create 3;
    is_sep_for = Hashtbl.create 3;
    is_end_for = Hashtbl.create 3;
    is_fragile = Hashtbl.create 3;
  }

  let fail_smash = "the left boundary of this box is fixed, it cannot be moved"
  let fail_par = "token '(' cannot be implicitly closed"
  let fail_brc = "token '{' cannot be implicitly closed"
  let fail_sqb = "token '[' cannot be implicitly closed"
  let fail_if  = "token 'if' cannot be implicitly closed"
  let fail_tab = "mixed space/tab indentation"

  let () =
    declare_box lang INIT ~lax:true ~iend:(FAIL fail_smash) ~ends:[EOF];
    declare_box lang LET ~isep:AND ~seps:[EQUAL] ~iend:ENDLET ~ends:[IN];
    declare_box lang FUN ~isep:AND ~seps:[EQUAL; COLON] ~iend:ENDFUN ~ends:[IN];
    declare_box lang REC ~isep:AND ~seps:[EQUAL; COLON] ~iend:ENDREC ~ends:[IN];
    declare_box lang EQUAL ~isep:SEMICOLON;
    declare_box lang RARROW ~isep:SEMICOLON;
    declare_box lang IN ~lax:true ~isep:SEMICOLON ~iend:ENDIN;
    declare_box lang DO ~isep:SEMICOLON ~iend:DONE;
    declare_box lang LEFTPAR ~isep:SEMICOLON ~iend:(FAIL fail_par) ~ends:[RIGHTPAR];
(*
    declare_box lang LEFTBRC ~isep:SEMICOLON ~iend:(FAIL fail_brc) ~ends:[RIGHTBRC];
*)
    declare_box lang LEFTSQ ~isep:SEMICOLON ~iend:(FAIL fail_sqb) ~ends:[RIGHTSQ];
    declare_box lang IF ~isep:SEMICOLON ~iend:(FAIL fail_if) ~ends:[THEN];
    declare_box lang THEN ~isep:SEMICOLON ~iend:ENDIF ~ends:[ELSE];
    declare_box lang ELSE ~lax:true ~isep:SEMICOLON ~iend:ENDIF;
    declare_box lang COLON ~isep:BAR ~ends:[EQUAL];
    declare_box lang WHERE ~isep:AND ~seps:[EQUAL; COLON] ~iend:ENDWHERE;
    declare_box lang WITH ~isep:BAR ~seps:[RARROW] ~iend:ENDWITH;

    declare_fragile lang COLON;
    declare_fragile lang BAR;
    declare_fragile lang RARROW;
    declare_fragile lang EQUAL

  type kind = Soft | Hard

  type box =
    | Box of kind
    | FreeStyle
    | Primed

  type block = token * int * box

  type state = {
    queue: token Queue.t;
    mutable lline: int;
    mutable lemit: token;
    mutable stack: block list;
    mutable ichar: char;
  }

  let create () = {
    queue = Queue.create ();
    lline = -1;
    lemit = SEMICOLON;
    stack = [ INIT, -1, Primed;
              INIT, -2, Box Hard ];
    ichar = '?';
  }

  let fail s = Loc.errorm "%a" Format.pp_print_text s

  let emit s = function
    | FAIL s -> fail s
    | t -> Queue.add t s.queue;
           s.lemit <- t

  let push st t tcol k = match k, st with
    | Box _, _ -> (t, tcol, k) :: st
    | _, (_, c, Box _) :: _ -> (t, c+1, k) :: st
    | _, (_, c, FreeStyle) :: _ -> (t, c, k) :: st
    | _, (_, _, Primed) :: _ -> assert false
    | _, [] -> assert false

  (* n the length of the suffix starting from the last seen candidate
     m tokens between the current position and the last seen candidate *)

  let unrelated t b = not (is_sep_for lang t b || is_end_for lang t b)

  let rec find_opener t tcol m n = function
    | (_, col, _) :: _ when col <= tcol && n > 0 -> n - 1
    | (b, _, _) :: st when unrelated t b -> find_opener t tcol (m + 1) n st
    | (_, col, _) :: st when tcol < col -> find_opener t tcol 0 (n + m + 1) st
    | _ -> if n > 0 then n - 1 else m

  exception Restart
  exception Retry

  let rec drop s n = match s.stack with
    | _ when n = 0 -> ()
    | [] -> assert false
    | (b, _, _) :: st ->
        ( match implicit_end lang b with
          | Some e ->
              emit s e;
              if is_opener lang e then (
                s.stack <- push st e 0 Primed;
                raise Restart )
          | None -> () );
        s.stack <- st;
        drop s (n - 1)

  let freestyle h =
    if h = Soft then FreeStyle else fail fail_smash

  let rec smash tcol = function
    | (_, col, _) :: _ as st when col <= tcol -> st
    | [_;_] | [_] -> fail fail_smash
    | (b, _, Box h) :: st ->
        push (smash tcol st) b 0 (freestyle h)
    | (b, _,  FreeStyle) :: st ->
        push (smash tcol st) b 0 FreeStyle
    | (_, _, Primed) :: _ -> assert false
    | [] -> assert false

  let rec cut tcol n = function
    | (_, col, _) :: _ as st when col <= tcol -> st, n
    | _ :: st -> cut tcol (n + 1) st
    | [] -> assert false

  let rec add s active t tcol tline =
(*     Printf.eprintf "[%s]%!" t; *)
    try
      if active && is_sep_end lang t then (
        let n = find_opener t tcol 0 0 s.stack in
        if n > 0 && is_fragile lang t then (
          let _,col,_ = List.nth s.stack (n - 1) in
          if col <= tcol then raise Retry );
        drop s n;
        let b, col, k, st = match s.stack with
          | (b, col, k) :: st -> b, col, k, smash tcol st
          | [] -> assert false in
        let st = if is_end_for lang t b then st else
          let k = match k with
            | Primed | FreeStyle -> FreeStyle
            | Box h when tcol < col -> freestyle h
            | Box _ -> k in
          push st b col k in
        s.stack <- st )
      else (
        let keep, n = cut tcol 0 s.stack in
        match s.stack, keep with
        | (r, _, Primed) :: ((_, bcol, Box _) :: _ as st), _
          when bcol = tcol && is_lax lang r ->
            s.stack <- push st r tcol (Box Soft)
        | _, (b, bcol, Box _) :: st when bcol = tcol ->
            drop s n; (* now s.stack == keep *)
            s.stack <- push st b tcol (Box Hard);
            ( match implicit_sep lang b with
              | Some sep when s.lemit <> sep -> emit s sep;
              | _ -> () )
        | (r, _, Primed) :: st, _ ->
            s.stack <- push (smash tcol st) r tcol (Box Soft)
        | st, _ ->
            s.stack <- smash tcol st );
      if active && is_opener lang t then
        s.stack <- push s.stack t 0 Primed;
      s.lline <- tline;
      emit s t
    with
    | Restart -> add s active t tcol tline
    | Retry   -> add s false  t tcol tline

  let add s lb ?(shift=0) t =
    let pos = lexeme_start_p lb in
    let col = pos.pos_cnum - pos.pos_bol in
    add s true t (2 * (col + shift)) pos.pos_lnum

  let check_indent s c = match s.ichar with
    | (' ' | '\t') as d when c <> d -> fail fail_tab
    | _ -> s.ichar <- c

}

let space = [' ' '\t']
let quote = '\''

let bin = ['0' '1']
let oct = ['0'-'7']
let dec = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']

let bin_sep = ['0' '1' '_']
let oct_sep = ['0'-'7' '_']
let dec_sep = ['0'-'9' '_']
let hex_sep = ['0'-'9' 'a'-'f' 'A'-'F' '_']

let lalpha = ['a'-'z']
let ualpha = ['A'-'Z']
let alpha  = ['a'-'z' 'A'-'Z']

let suffix = (alpha | quote* dec_sep)* quote*
let lident = ['a'-'z' '_'] suffix
let uident = ['A'-'Z'] suffix

let core_suffix = quote alpha suffix
let core_lident = lident core_suffix+
let core_uident = uident core_suffix+

let op_char_0 = ['!' '?']
let op_char_1 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_2 = ['*' '/' '\\' '%']
let op_char_3 = ['+' '-']
let op_char_4 = ['=' '<' '>' '~']
let op_char_12 = op_char_1 | op_char_2
let op_char_123 = op_char_12 | op_char_3
let op_char_1234 = op_char_123 | op_char_4

rule token st = parse
  | space+
      { token st lexbuf }
  | ";;" [^ '\r' '\n' ]*
      { token st lexbuf }
  | '\r'? '\n'
      { new_line lexbuf; start st lexbuf }
  | "[@" space* ([^ ' ' '\t' '\r' '\n' ']']+ (' '+ [^ ' ' '\t' '\r' '\n' ']']+)* as lbl) space* ']'
      { add st lexbuf (ATTRIBUTE lbl) }
  | lident as id
      { add st lexbuf (try Hashtbl.find keywords id with Not_found -> LIDENT id) }
  | core_lident as id
      { add st lexbuf (CORE_LIDENT id) }
  | uident as id
      { add st lexbuf (UIDENT id) }
  | core_uident as id
      { add st lexbuf (CORE_UIDENT id) }
  | dec dec_sep* as s
      { let l = Number.(int_literal ILitDec ~neg:false (Lexlib.remove_underscores s)) in
        add st lexbuf (INTEGER l) }
  | '0' ['x' 'X'] (hex hex_sep* as s)
      { let l = Number.(int_literal ILitHex ~neg:false (Lexlib.remove_underscores s)) in
        add st lexbuf (INTEGER l) }
  | '0' ['o' 'O'] (oct oct_sep* as s)
      { let l = Number.(int_literal ILitOct ~neg:false (Lexlib.remove_underscores s)) in
        add st lexbuf (INTEGER l) }
  | '0' ['b' 'B'] (bin bin_sep* as s)
      { let l = Number.(int_literal ILitBin ~neg:false (Lexlib.remove_underscores s)) in
        add st lexbuf (INTEGER l) }
  | (dec+ as s) ".."
      { let l = Number.(int_literal ILitDec ~neg:false s) in
        add st lexbuf (INTEGER l);
        add st lexbuf ~shift:(String.length s) DOTDOT; }
  | '0' ['x' 'X'] (hex+ as s) ".."
      { let l = Number.(int_literal ILitHex ~neg:false s) in
        add st lexbuf (INTEGER l);
        add st lexbuf ~shift:(String.length s + 2) DOTDOT; }
  | (dec+ as i)     ("" as f)    ['e' 'E'] (['-' '+']? dec+ as e)
  | (dec+ as i) '.' (dec* as f) (['e' 'E'] (['-' '+']? dec+ as e))?
  | (dec* as i) '.' (dec+ as f) (['e' 'E'] (['-' '+']? dec+ as e))?
      { let e = Opt.map Lexlib.remove_leading_plus e in
        let l = Number.real_literal ~radix:10 ~neg:false ~int:i ~frac:f ~exp:e in
        add st lexbuf (REAL l) }
  | '0' ['x' 'X'] (hex+ as i) ("" as f) ['p' 'P'] (['-' '+']? dec+ as e)
  | '0' ['x' 'X'] (hex+ as i) '.' (hex* as f) (['p' 'P'] (['-' '+']? dec+ as e))?
  | '0' ['x' 'X'] (hex* as i) '.' (hex+ as f) (['p' 'P'] (['-' '+']? dec+ as e))?
      { let e = Opt.map Lexlib.remove_leading_plus e in
        let l = Number.real_literal ~radix:16 ~neg:false ~int:i ~frac:f ~exp:e in
        add st lexbuf (REAL l) }
  | "'" (lalpha suffix as id)
      { add st lexbuf (QUOTE_LIDENT id) }
  | "_"
      { add st lexbuf UNDERSCORE }
  | ","
      { add st lexbuf COMMA }
  | "("
      { add st lexbuf LEFTPAR }
  | ")"
      { add st lexbuf RIGHTPAR }
(*
  | "{"
      { add st lexbuf LEFTBRC }
  | "}"
      { add st lexbuf RIGHTBRC }
*)
  | ":"
      { add st lexbuf COLON }
  | ";"
      { add st lexbuf SEMICOLON }
  | "->"
      { add st lexbuf RARROW }
  | "->'" (lalpha suffix as id)
      { add st lexbuf RARROW;
        add st lexbuf ~shift:2 (QUOTE_LIDENT id) }
  | "<-"
      { add st lexbuf LARROW }
(*
  | "<->"
      { add st lexbuf LRARROW }
*)
  | "&&"
      { add st lexbuf AMPAMP }
  | "||"
      { add st lexbuf BARBAR }
  | "."
      { add st lexbuf DOT }
  | ".."
      { add st lexbuf DOTDOT }
  | "&"
      { add st lexbuf AMP }
  | "|"
      { add st lexbuf BAR }
(*
  | "<"
      { add st lexbuf LT }
  | ">"
      { add st lexbuf GT }
  | "<>"
      { add st lexbuf LTGT }
*)
  | "="
      { add st lexbuf EQUAL }
  | "-"
      { add st lexbuf MINUS }
  | "["
      { add st lexbuf LEFTSQ }
  | "]"
      { add st lexbuf RIGHTSQ }
  | "]" (quote+ as s)
      { add st lexbuf (RIGHTSQ_QUOTE s) }
  | ")" ('\'' alpha suffix core_suffix* as s)
      { add st lexbuf (RIGHTPAR_QUOTE s) }
  | ")" ('_' alpha suffix core_suffix* as s)
      { add st lexbuf (RIGHTPAR_USCORE s) }
  | op_char_0 op_char_1* quote* as s
      { add st lexbuf (OP0 s) }
  | op_char_1+ quote* as s
      { add st lexbuf (OP1 s) }
  | op_char_12* op_char_2 op_char_12* quote* as s
      { add st lexbuf (OP2 s) }
  | op_char_123* op_char_3 op_char_123* quote* as s
      { add st lexbuf (OP3 s) }
  | op_char_1234* op_char_4 op_char_1234* quote* as s
      { add st lexbuf (OP4 s) }
(*
  | "\""
      { let start_p = lexbuf.lex_start_p in
        let start_pos = lexbuf.lex_start_pos in
        let s = Lexlib.string lexbuf in
        lexbuf.lex_start_p <- start_p;
        lexbuf.lex_start_pos <- start_pos;
        add st lexbuf (STRING s) }
*)
  | eof
      { add st lexbuf EOF }
  | _ as c
      { Lexlib.illegal_character c lexbuf }

and start st = parse
  | ' '+
      { check_indent st ' ' ; token st lexbuf }
  | '\t'+
      { check_indent st '\t' ; token st lexbuf }
  | ' '+ '\t' | '\t'+ ' '
      { fail fail_tab }
  | ""
      { token st lexbuf }

{
  let next st lb =
    if Queue.is_empty st.queue then token st lb;
    Queue.pop st.queue

  let parse file c =
    let st = create () in
    let lb = from_channel c in
    Why3.Loc.set_file file lb;
    Why3.Loc.with_location (start st) lb;
    Why3.Loc.with_location (Mome_parser.top_level (next st)) lb

(*
  let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | _ -> raise exn)
*)

}

(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format

let print_header fmt ?(title="") ?css () =
  fprintf fmt "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01//EN\"@\n\"http://www.w3.org/TR/html4/strict.dtd\">@\n<html>@\n<head>@\n<meta http-equiv=\"Content-Type\" content=\"text/html;charset=utf-8\">@\n";
  begin match css with
    | None -> ()
    | Some f -> fprintf fmt
        "<link rel=\"stylesheet\" href=\"%s\" type=\"text/css\">@\n" f
  end;
  fprintf fmt "<title>%s</title>@\n" title;
  fprintf fmt "</head>@\n<body>@\n"

let print_footer fmt () =
  fprintf fmt "<hr>@\n<p>Generated by why3doc %s</p>@\n</body>@\n</html>@."
    Why3.Config.version

let style_css fname =
  let c = open_out fname in
  output_string c
 ".why3doc a:visited { color: #416DFF; text-decoration: none }\
\n.why3doc a:link { color: #416DFF; text-decoration: none }\
\n.why3doc a:hover { color: red; text-decoration: none; background-color: #5FFF88 }\
\n.why3doc a:active { color: red; text-decoration: underline }\
\n.why3doc .attribute { color: #bbb }\
\n.why3doc .comment { color: #990000 }\
\n.why3doc .keyword { color: purple; font-weight: bold }\
\n.why3doc .superscript { font-size: smaller }\
\n.why3doc .subscript { font-size: smaller }\
\n.why3doc .warning { color: red; font-weight: bold }\
\n.why3doc .info { margin-left: 3em; margin-right: 3em; background-color: #dcc; }\
\n.why3doc .info > p:first-child { margin-top: 0 }\
\n.why3doc code { color: #465F91 }\
\n.why3doc h1 { font-size: 20pt; border: 1px solid #000000; margin: 10pt 0; text-align: center; background-color: #90BDFF; padding: 10pt }\
\n.why3doc h2 { font-size: 18pt; border: 1px solid #000000; margin: 8pt 0; text-align: left; background-color: #90DDFF; padding: 8pt }\
\n.why3doc h3 { font-size: 15pt; border: 1px solid #000000; margin: 6pt 0; text-align: left; background-color: #90EDFF; padding: 6pt }\
\n.why3doc h4 { font-size: 12pt; border: 1px solid #000000; margin: 4pt 0; text-align: left; background-color: #90FDFF; padding: 4pt }\
\n.why3doc h5 { font-size: 11pt; border: 1px solid #000000; margin: 2pt 0; text-align: left; background-color: #90FEFF; padding: 2pt }\
\n.why3doc h6 { font-size: 10pt; border: 1px solid #000000; margin: 0pt 0; text-align: left; background-color: #90FFFF; padding: 0pt }\
\n.why3doc .typetable { border-style: hidden }\
\n.why3doc .indextable { border-style: hidden }\
\n.why3doc .paramstable { border-style: hidden; padding: 5pt 5pt }\
\n.why3doc body { background-color: white }\
\n.why3doc tr { background-color: white }\
\n.why3doc td.typefieldcomment { background-color: #FFFFFF }\
\n.why3doc pre { margin-top: 0; margin-bottom: 0.5ex }\
\n.why3doc div.sig_block { margin-left: 2em }\
\n";
  close_out c

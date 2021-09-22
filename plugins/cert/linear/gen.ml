open Format

let rec print_pred i fmt n =
  if i <= n then begin
      fprintf fmt "predicate p%dp@ " i;
      print_pred (i+1) fmt n
    end

let rec print_goal i fmt n =
  if i < n then begin
      fprintf fmt "(p%dp -> p%dp) ->@ " i (i+1);
      print_goal (i+1) fmt n
    end


let _ =
  let n = Sys.argv.(1) |> int_of_string in
  let filename = sprintf "linear%d.mlw" n in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "@[<v>%a @ @]goal G : @[p1p ->@ %ap%dp@]@."
          (print_pred 1) n
          (print_goal 1) n
          n;
  close_out oc



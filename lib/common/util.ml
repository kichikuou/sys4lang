open Base

let parse_qualified_name name =
  match String.rindex name ':' with
  | Some i when i > 0 && Char.(String.get name (i - 1) = ':') ->
      let left = String.sub name ~pos:0 ~len:(i - 1) in
      let right =
        String.sub name ~pos:(i + 1) ~len:(String.length name - i - 1)
      in
      (Some left, right)
  | _ -> (None, name)

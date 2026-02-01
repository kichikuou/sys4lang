open Base
open System4_lsp

let test_project_dir = Stdlib.Filename.concat (Stdlib.Sys.getcwd ()) "testdata"

let initialize_project () =
  let proj = Project.create ~read_file:Stdio.In_channel.read_all in
  let pjePath = Stdlib.Filename.concat test_project_dir "default.pje" in
  let options = { Types.InitializationOptions.default with pjePath } in
  Project.initialize proj options;
  Project.initial_scan proj;
  proj

let load_jaf proj path =
  let jaf_text = Stdio.In_channel.read_all path in
  List.iter (Project.update_document proj ~path jaf_text) ~f:(fun d ->
      Stdio.printf "(%d, %d) - (%d, %d) " d.range.start.line
        d.range.start.character d.range.end_.line d.range.end_.character;
      match d.message with
      | `String message -> Stdio.print_endline message
      | _ -> Stdio.print_endline "?");
  jaf_text

let%expect_test "get_hover" =
  let proj = initialize_project () in
  let path = Stdlib.Filename.concat test_project_dir "hover.jaf" in
  let jaf_text = load_jaf proj path in
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern:"^hover" with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d: " pos.line pos.character;
          let hover = Project.get_hover proj ~path pos in
          match hover with
          | Some { contents = `MarkupContent { value; _ }; _ } ->
              Stdio.print_endline value
          | _ -> Stdio.print_endline "No hover info")
      | None -> ());
  [%expect {|
    3:11: int
    8:11: string
    |}]

let definition_test
    (getdef :
      Project.t ->
      path:string ->
      Lsp.Types.Position.t ->
      Lsp.Types.Locations.t option) pattern =
  let proj = initialize_project () in
  let path = Stdlib.Filename.concat test_project_dir "definition.jaf" in
  let jaf_text = load_jaf proj path in
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d: " pos.line pos.character;
          let locs = getdef proj ~path pos in
          match locs with
          | Some (`Location [ loc ]) ->
              let def_path = Lsp.Uri.to_path loc.uri in
              let def_text = Stdio.In_channel.read_all def_path in
              let def_lines = String.split_lines def_text in
              let start_line = List.nth_exn def_lines loc.range.start.line in
              let text =
                String.sub start_line ~pos:loc.range.start.character
                  ~len:(loc.range.end_.character - loc.range.start.character)
              in
              Stdio.printf "%s:%d:%d-%d \"%s\"\n"
                (Stdlib.Filename.basename def_path)
                loc.range.start.line loc.range.start.character
                loc.range.end_.character text
          | _ -> Stdio.print_endline "No definition found")
      | None -> ())

let%expect_test "get_definition" =
  definition_test Project.get_definition "^definition";
  [%expect
    {|
    1:11: definition.jaf:0:21-26 "int x"
    6:11: globals.jaf:0:4-14 "global_int"
    13:5: definition.jaf:10:0-17 "void foo(void) {}"
    |}]

let%expect_test "get_type_definition" =
  definition_test Project.get_type_definition "^type_definition";
  [%expect
    {|
    18:11: classes.jaf:0:0-20 "struct S { int x; };"
    23:4: classes.jaf:1:0-23 "functype void ft(void);"
    |}]

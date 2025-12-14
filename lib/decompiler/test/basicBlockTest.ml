(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://gnu.org/licenses/>.
 *)

open Base
open Decompiler

let make_function ?(vars = [||]) ?(return_type = Type.Void) name =
  Ain.Function.
    {
      address = 0;
      name;
      is_label = false;
      is_lambda = false;
      capture = false;
      return_type;
      vars;
      nr_args = 0;
      crc = 0l;
    }

let decompile_test ?(func = [||]) var_types insns =
  Ain.ain.func <- func;
  let rev_insns = List.rev insns in
  let end_addr = fst (List.hd_exn rev_insns) + 2 in
  let _, code =
    List.fold rev_insns ~init:(end_addr, [])
      ~f:(fun (end_addr, acc) (addr, insn) ->
        (addr, { Loc.txt = insn; addr; end_addr } :: acc))
  in
  let vars =
    Array.of_list_mapi var_types ~f:(fun i type_ ->
        Ain.Variable.
          {
            name = Printf.sprintf "var%d" i;
            name2 = "";
            type_;
            init_val = None;
            group_index = 0;
          })
  in
  let func : CodeSection.function_t =
    {
      func = make_function "testfunc" ~vars;
      name = "testfunc";
      struc = None;
      end_addr;
      code;
      lambdas = [];
      parent = None;
    }
  in
  let bbs = BasicBlock.create func in
  Stdio.print_endline ([%show: BasicBlock.t list] bbs)

let%expect_test "return 1 + 2;" =
  decompile_test []
    [
      (0x00000006, PUSH 1l);
      (0x0000000C, PUSH 2l);
      (0x00000012, ADD);
      (0x00000014, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 22; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt = (Return (Some (BinaryOp (ADD, (Number 1l), (Number 2l)))));
           addr = 6; end_addr = 22 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 3 && 4;" =
  decompile_test []
    [
      (0x00000006, PUSH 3l);
      (0x0000000C, IFZ 0x2a);
      (0x00000012, PUSH 4l);
      (0x00000018, IFZ 0x2a);
      (0x0000001E, PUSH 1l);
      (0x00000024, JUMP 0x30);
      (0x0000002A, PUSH 0l);
      (0x00000030, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 50; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return (Some (BinaryOp (PSEUDO_LOGAND, (Number 3l), (Number 4l)))));
           addr = 6; end_addr = 50 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 3 || 4;" =
  decompile_test []
    [
      (0x00000006, PUSH 3l);
      (0x0000000C, IFNZ 0x2a);
      (0x00000012, PUSH 4l);
      (0x00000018, IFNZ 0x2a);
      (0x0000001E, PUSH 0l);
      (0x00000024, JUMP 0x30);
      (0x0000002A, PUSH 1l);
      (0x00000030, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 50; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return (Some (BinaryOp (PSEUDO_LOGOR, (Number 3l), (Number 4l)))));
           addr = 6; end_addr = 50 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return (2 && 3) || (4 && 5);" =
  decompile_test []
    [
      (0x00000006, PUSH 2l);
      (0x0000000C, IFZ 0x2a);
      (0x00000012, PUSH 3l);
      (0x00000018, IFZ 0x2a);
      (0x0000001E, PUSH 1l);
      (0x00000024, JUMP 0x30);
      (0x0000002A, PUSH 0l);
      (0x00000030, IFNZ 0x72);
      (0x00000036, PUSH 4l);
      (0x0000003C, IFZ 0x5a);
      (0x00000042, PUSH 5l);
      (0x00000048, IFZ 0x5a);
      (0x0000004E, PUSH 1l);
      (0x00000054, JUMP 0x60);
      (0x0000005A, PUSH 0l);
      (0x00000060, IFNZ 0x72);
      (0x00000066, PUSH 0l);
      (0x0000006C, JUMP 0x78);
      (0x00000072, PUSH 1l);
      (0x00000078, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 122; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return
              (Some (BinaryOp (PSEUDO_LOGOR,
                       (BinaryOp (PSEUDO_LOGAND, (Number 2l), (Number 3l))),
                       (BinaryOp (PSEUDO_LOGAND, (Number 4l), (Number 5l)))))));
           addr = 6; end_addr = 122 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 2; return 3 || 4;" =
  decompile_test []
    [
      (0x00000006, PUSH 2l);
      (0x0000000C, RETURN);
      (0x0000000E, PUSH 3l);
      (0x00000014, IFNZ 0x32);
      (0x0000001A, PUSH 4l);
      (0x00000020, IFNZ 0x32);
      (0x00000026, PUSH 0l);
      (0x0000002C, JUMP 0x38);
      (0x00000032, PUSH 1l);
      (0x00000038, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 58; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return (Some (BinaryOp (PSEUDO_LOGOR, (Number 3l), (Number 4l)))));
           addr = 14; end_addr = 58 };
          { txt = (Return (Some (Number 2l))); addr = 6; end_addr = 14 }]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 1 + (2 && 3);" =
  decompile_test []
    [
      (0x00000006, PUSH 1l);
      (0x0000000C, PUSH 2l);
      (0x00000012, IFZ 0x30);
      (0x00000018, PUSH 3l);
      (0x0000001E, IFZ 0x30);
      (0x00000024, PUSH 1l);
      (0x0000002A, JUMP 0x36);
      (0x00000030, PUSH 0l);
      (0x00000036, ADD);
      (0x00000038, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 58; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return
              (Some (BinaryOp (ADD, (Number 1l),
                       (BinaryOp (PSEUDO_LOGAND, (Number 2l), (Number 3l)))))));
           addr = 6; end_addr = 58 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 1 + (2 || 3);" =
  decompile_test []
    [
      (0x00000006, PUSH 1l);
      (0x0000000C, PUSH 2l);
      (0x00000012, IFNZ 0x30);
      (0x00000018, PUSH 3l);
      (0x0000001E, IFNZ 0x30);
      (0x00000024, PUSH 0l);
      (0x0000002A, JUMP 0x36);
      (0x00000030, PUSH 1l);
      (0x00000036, ADD);
      (0x00000038, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 58; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return
              (Some (BinaryOp (ADD, (Number 1l),
                       (BinaryOp (PSEUDO_LOGOR, (Number 2l), (Number 3l)))))));
           addr = 6; end_addr = 58 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 1 ? 2 : 3;" =
  decompile_test []
    [
      (0x00000006, PUSH 1l);
      (0x0000000C, IFZ 0x1e);
      (0x00000012, PUSH 2l);
      (0x00000018, JUMP 0x24);
      (0x0000001E, PUSH 3l);
      (0x00000024, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 38; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return (Some (TernaryOp ((Number 1l), (Number 2l), (Number 3l)))));
           addr = 6; end_addr = 38 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 1 ? 2 : 3 ? 4 : 5;" =
  decompile_test []
    [
      (0x00000006, PUSH 1l);
      (0x0000000C, IFZ 0x1e);
      (0x00000012, PUSH 2l);
      (0x00000018, JUMP 0x3c);
      (0x0000001E, PUSH 3l);
      (0x00000024, IFZ 0x36);
      (0x0000002A, PUSH 4l);
      (0x00000030, JUMP 0x3c);
      (0x00000036, PUSH 5l);
      (0x0000003C, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 62; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return
              (Some (TernaryOp ((Number 1l), (Number 2l),
                       (TernaryOp ((Number 3l), (Number 4l), (Number 5l)))))));
           addr = 6; end_addr = 62 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return 1 + (2 ? 3 : 4 ? 5 : 6);" =
  decompile_test []
    [
      (0x00000006, PUSH 1l);
      (0x0000000C, PUSH 2l);
      (0x00000012, IFZ 0x24);
      (0x00000018, PUSH 3l);
      (0x0000001E, JUMP 0x42);
      (0x00000024, PUSH 4l);
      (0x0000002A, IFZ 0x3c);
      (0x00000030, PUSH 5l);
      (0x00000036, JUMP 0x42);
      (0x0000003C, PUSH 6l);
      (0x00000042, ADD);
      (0x00000044, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 70; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return
              (Some (BinaryOp (ADD, (Number 1l),
                       (TernaryOp ((Number 2l), (Number 3l),
                          (TernaryOp ((Number 4l), (Number 5l), (Number 6l)))))
                       ))));
           addr = 6; end_addr = 70 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return var1 ?? var2;" =
  decompile_test [ Ref String; Ref String ]
    [
      (0x00000006, SH_LOCALREF 0x0);
      (0x0000000C, DUP);
      (0x0000000E, PUSH (-1l));
      (0x00000014, EQUALE);
      (0x00000016, IFZ 0x24);
      (0x0000001C, POP);
      (0x0000001E, SH_LOCALREF 0x1);
      (0x00000024, DUP);
      (0x00000026, SP_INC);
      (0x00000028, RETURN);
    ];
  [%expect
    {|
    [{ addr = 6; end_addr = 42; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return
              (Some (BinaryOp (PSEUDO_NULL_COALESCE,
                       (Deref
                          (PageRef (LocalPage,
                             { Ain.Variable.name = "var0"; name2 = "";
                               type_ = (Type.Ref Type.String); init_val = None;
                               group_index = 0 }
                             ))),
                       (Deref
                          (PageRef (LocalPage,
                             { Ain.Variable.name = "var1"; name2 = "";
                               type_ = (Type.Ref Type.String); init_val = None;
                               group_index = 0 }
                             )))
                       ))));
           addr = 6; end_addr = 42 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "var?.void_method();" =
  let func : Ain.Function.t array = [| make_function "void_method" |] in
  decompile_test ~func [ Ref (Struct 0) ]
    [
      (0x0000000E, SH_LOCALREF 0x0);
      (0x00000014, DUP);
      (0x00000016, PUSH (-1l));
      (0x0000001C, EQUALE);
      (0x0000001E, IFNZ 0x36);
      (0x00000024, CALLMETHOD 0);
      (0x0000002A, PUSH 0l);
      (0x00000030, JUMP 0x3e);
      (0x00000036, POP);
      (0x00000038, PUSH (-1l));
      (0x0000003E, POP);
      (0x00000040, RETURN);
    ];
  [%expect
    {|
    [{ addr = 14; end_addr = 66; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt = (Return None); addr = 42; end_addr = 66 };
          { txt =
            (Expression
               (Call (
                  (Method (
                     (Option
                        (Deref
                           (PageRef (LocalPage,
                              { Ain.Variable.name = "var0"; name2 = "";
                                type_ = (Type.Ref (Type.Struct 0));
                                init_val = None; group_index = 0 }
                              )))),
                     { Ain.Function.address = 0; name = "void_method";
                       is_label = false; is_lambda = false; capture = false;
                       return_type = Type.Void; vars = [||]; nr_args = 0;
                       crc = 0l }
                     )),
                  [])));
            addr = 14; end_addr = 42 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

let%expect_test "return var?.int_method() ?? 42;" =
  let func : Ain.Function.t array =
    [| make_function "int_method" ~return_type:Type.Int |]
  in
  decompile_test ~func [ Ref (Struct 0) ]
    [
      (0x0000001C, SH_LOCALREF 0x0);
      (0x00000022, DUP);
      (0x00000024, PUSH (-1l));
      (0x0000002A, EQUALE);
      (0x0000002C, IFNZ 0x44);
      (0x00000032, CALLMETHOD 0);
      (0x00000038, PUSH 0l);
      (0x0000003E, JUMP 0x52);
      (0x00000044, POP);
      (0x00000046, PUSH (-1l));
      (0x0000004C, PUSH (-1l));
      (0x00000052, PUSH (-1l));
      (0x00000058, EQUALE);
      (0x0000005A, IFZ 0x68);
      (0x00000060, POP);
      (0x00000062, PUSH 42l);
      (0x00000068, RETURN);
    ];
  [%expect
    {|
    [{ addr = 28; end_addr = 106; labels = [];
       code =
       ({ txt = Seq; addr = -1; end_addr = -1 },
        [{ txt =
           (Return
              (Some (BinaryOp (PSEUDO_NULL_COALESCE,
                       (Call (
                          (Method (
                             (Option
                                (Deref
                                   (PageRef (LocalPage,
                                      { Ain.Variable.name = "var0"; name2 = "";
                                        type_ = (Type.Ref (Type.Struct 0));
                                        init_val = None; group_index = 0 }
                                      )))),
                             { Ain.Function.address = 0; name = "int_method";
                               is_label = false; is_lambda = false;
                               capture = false; return_type = Type.Int;
                               vars = [||]; nr_args = 0; crc = 0l }
                             )),
                          [])),
                       (Number 42l)))));
           addr = 28; end_addr = 106 }
          ]);
       nr_jump_srcs = 0 }
      ]
    |}]

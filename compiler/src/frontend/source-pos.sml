(* Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

 (* Modified by Gian Perrone for the ml2pp0 compiler *)

structure SourcePos: SOURCE_POS =
struct

datatype t = T of {column: int,
                   file: string,
                   line: int}

local
   fun f g (T r) = g r
in
   val column = f #column
   val line = f #line
end

fun equals (T r, T r') = r = r'
val _ = equals

fun make {column, file, line} =
   T {column = column,
      file = file,
      line = line}

fun getLib (T {file, ...}) = NONE

fun file (p as T {file, ...}) = file

val bogus = T {column = ~1,
               file = "<bogus>",
               line = ~1}

fun toString (p as T {column, line, ...}) =
   concat [file p, " ", Int.toString line, ".", Int.toString column]

fun posToString (T {line, column, ...}) =
   concat [Int.toString line, ".", Int.toString column]

end

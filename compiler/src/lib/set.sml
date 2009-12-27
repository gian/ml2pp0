structure Set = struct
   type ''a set = ''a list (* [a1,...,an] with ai <> aj for i <> j *)

   val empty = [];

   fun member(x, ys) = List.exists (fn y => x = y) ys;

   fun insert(x,ys) = if member(x,ys) then ys else x::ys;

   fun union(xs, ys) = List.foldl insert ys xs;

   fun inter(xs, ys) = List.filter (fn x => member(x, ys)) xs;

   fun diff(xs, ys)  = List.filter (fn x => not (member(x, ys))) xs;

   fun delete([], _)    = []
     | delete(x::xs, y) = if x=y then xs else x::delete(xs,y);  

   fun subset(xs, ys) = List.all (fn x => member(x, ys)) xs;
 
   fun equal(xs, ys) = subset(xs, ys) andalso subset(ys, xs);

   fun fromList xs = List.foldl insert empty xs;

   fun toList xs = xs;

   fun card xs = List.length xs;
 
   fun filter p xs = List.filter p xs;

   fun exists p xs = List.exists p xs;

   fun all p xs = List.all p xs;

   fun find p xs = List.find p xs;

   fun map f s = List.foldl (fn (y,ys) => insert(f y, ys)) empty s;

   fun fold f = List.foldl f;

   fun split [] = NONE | split (x::xs) = SOME(x,xs);

   fun singleton a = [a];
end


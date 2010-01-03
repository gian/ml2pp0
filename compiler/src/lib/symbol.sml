signature SYMBOL =
sig
  eqtype symbol
  val symbol : string -> symbol
  val name : symbol -> string
  val hash : symbol -> int
  type 'a table
  val empty : 'a table
  val enter : 'a table * symbol * 'a -> 'a table
  val look  : 'a table * symbol -> 'a option
  val items : 'a table -> 'a list
  val keys  : 'a table -> (IntBinaryMap.Key.ord_key * 'a) list

  val toString : symbol -> string
  val fromString : string -> symbol

  val asterisk : symbol
  val equal : symbol
end

structure Symbol :> SYMBOL =
struct

  type symbol = string * int

  structure H = HashTable

  exception Symbol
  val nextsym = ref 0
  val sizeHint = 128
  val hashtable : (string,int) H.hash_table = 
		H.mkTable(HashString.hashString, op = ) (sizeHint,Symbol)
  
  fun symbol name =
      case H.find hashtable name
       of SOME i => (name,i)
        | NONE => let val i = !nextsym
	           in nextsym := i+1;
		      H.insert hashtable (name,i);
		      (name,i)
		  end

  fun name(s,n) = s
  fun hash(s,n) = n

  val toString = name

  val fromString = symbol

  structure Table = IntMapTable(type key = symbol
				fun getInt(s,n) = n)

  type 'a table= 'a Table.table
  val empty = Table.empty
  val enter = Table.enter
  val look = Table.look
  val items = Table.items
  val keys = Table.keys

  val asterisk = fromString "*"
  val equal = fromString "="
end


structure Symbol =
struct

	type symbol = string

	fun toString s = s

	fun fromString s = s

	val asterisk = "*";
	val equal = "=";
end

(** Operations that can be performed on (binary) words. *)

open Bap.Std

val add_exact : word -> word -> word
val mul_exact : word -> word -> word
val succ_exact : word -> word
val lshift_exact : word -> int -> word


val cdiv : word -> word -> word

val gt_int : word -> int -> bool
val lt_int : word -> int -> bool

val is_one : word -> bool

val bounded_gcd : word -> word -> word

val bounded_lcm : word -> word -> word option

val bounded_diophantine : word -> word -> word -> (word * word) option

val factor_2s : word -> word * int

val count_initial_1s : word -> int

val lead_1_bit : word -> int option

val min : word -> word -> word
val max : word -> word -> word

(** Computes the domain size, i.e., the number of elements that can be
    represented with a CLP of words that are all [i]-bits wide.

    The result is thus 2^i. For instance, with 3-bits, you can get represent
    2^3 elements, i.e., 8 elements (the numbers 0--7, for instance).

    The result is returned as a binary word, of a specified [width].
    So, [dom_size i ~width:w] returns 2^i, represented as a [w]-bit word.
    For example, [dom_size 3 ~width:4] returns [b1000]. If you omit [~width],
    the default is [i + 1].

    Note that if you specify a width [w] and an [i] such that [i = w], then
    [dom_size] will return zero. For example, [dom_size 3 ~width:3] will
    return [b000]. With 3 bits, you can represent 8 elements [b1000], but
    you need 4 bits (rather than [~width:3]) to represent 8.

    So one should always invoke this [dom_size] function with [w > i],
    in order to guarantee that the result can be represented by the
    returned word. *)    
val dom_size : ?width : int -> int -> word

val cap_at_width : width:int -> word -> word

val add_bit : word -> word

val endian_string : Word.endian -> string

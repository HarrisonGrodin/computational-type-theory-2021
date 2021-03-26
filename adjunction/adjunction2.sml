structure Void :>
  sig
    type void
    val absurd : void -> 'a
  end =
  struct
    datatype void = Void of void
    fun absurd (Void v) = absurd v
  end

open Void Either


exception TypeError

signature FORM =
  sig
    type 'a ty
    type 't intro
    type 't elim
    val beta : 't intro * 't elim -> 't
    val eta  : 'a ty -> 't elim intro
    val map_i : ('a -> 'b) -> 'a intro -> 'b intro
    val map_e : ('a -> 'b) -> 'a elim  -> 'b elim
  end

functor Join (
  structure F1 : FORM
  structure F2 : FORM
) : FORM =
  struct
    type 'a ty = ('a F1.ty, 'a F2.ty) either
    type 't intro = ('t F1.intro, 't F2.intro) either
    type 't elim  = ('t F1.elim , 't F2.elim ) either
    val beta =
      fn (INL intro, INL elim) => F1.beta (intro, elim)
       | (INR intro, INR elim) => F2.beta (intro, elim)
    val eta =
      fn INL a => INL (F1.map_i INL (F1.eta a))
       | INR a => INR (F2.map_i INR (F2.eta a))
    val map_i = fn f => map (F1.map_i f, F2.map_i f)
    val map_e = fn f => map (F1.map_e f, F2.map_e f)
  end

structure Unit : FORM =
  struct
    type 'a ty = unit
    type 't intro = unit
    type 't elim  = void

    val beta = fn ((), v) => absurd v
    val eta  = fn () => ()
    val map_i = fn _ => Fn.id
    val map_e = fn _ => Fn.id
  end

structure Prod : FORM =
  struct
    type 'a ty = 'a * 'a
    type 't intro = 't * 't
    type 't elim = bool  (* fst or snd *)
    val beta =
      fn ((e1, _), true ) => e1
       | ((_, e2), false) => e2
    val eta = fn _ => (false, true)
    val map_i = fn f => fn (e1, e2) => (f e1, f e2)
    val map_e = fn _ => Fn.id
  end

functor Exp (F : FORM) =
  struct
    structure F = F
    datatype t = Intro of t F.intro | Elim of t * t F.elim

    val rec beta =
     fn Intro intro     => Intro (F.map_i beta intro)
      | Elim  (e, elim) => (
          case beta e of
            Intro intro => F.beta (intro, elim)
          | e'          => Elim (e', elim)
        )
  end

structure E =
  Exp (
    Join (
      structure F1 = Unit
      structure F2 = Prod
    )
  )

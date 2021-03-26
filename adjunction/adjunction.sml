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
    type 't intro
    type 't elim
    val beta : 't intro elim -> 't
    val eta  : 't -> 't elim intro
    val map_i : ('a -> 'b) -> 'a intro -> 'b intro
    val map_e : ('a -> 'b) -> 'a elim  -> 'b elim
  end

functor Join (
  structure F1 : FORM
  structure F2 : FORM
) : FORM =
  struct
    type 't intro = ('t F1.intro, 't F2.intro) either
    type 't elim  = ('t F1.elim , 't F2.elim ) either
    val beta =
      fn INL elim => F1.beta (F1.map_e (fn INL intro => intro | INR _ => raise TypeError) elim)
       | INR elim => F2.beta (F2.map_e (fn INR intro => intro | INL _ => raise TypeError) elim)
    val eta = fn t => raise Fail "TODO"
    val map_i = fn f => map (F1.map_i f, F2.map_i f)
    val map_e = fn f => map (F1.map_e f, F2.map_e f)
  end

structure Unit : FORM =
  struct
    type 't intro = unit
    type 't elim  = void

    val beta = Void.absurd
    val eta  = fn _ => ()
    val map_i = fn _ => Fn.id
    val map_e = fn _ => Fn.id
  end

structure Prod : FORM =
  struct
    type 't intro = 't * 't
    type 't elim = ('t, 't) either  (* fst or snd *)
    val beta =
      fn INL (e1, _ ) => e1
       | INR (_ , e2) => e2
    val eta = fn t => (INL t, INR t)
    val map_i = fn f => fn (e1, e2) => (f e1, f e2)
    val map_e = fn f => map (f, f)
  end

functor Exp (F : FORM) =
  struct
    datatype t = Intro of t F.intro | Elim of t F.elim

    val rec beta =
     fn Intro e => Intro (F.map_i beta e)
      | Elim  e => (
          let val e' = F.map_e beta e in
            F.beta (F.map_e (fn Intro i => i | Elim _ => raise Div) e')
              handle Div => Elim e'
          end
        )
  end

structure E =
  Exp (
    Join (
      structure F1 = Unit
      structure F2 = Prod
    )
  )

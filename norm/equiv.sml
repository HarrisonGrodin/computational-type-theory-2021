structure Variable :>
  sig
    type t
    val new : unit -> t
    val eq : t * t -> bool
    val compare : t * t -> order
  end =
  struct
    type t = int

    val counter = ref 0
    val new = fn () => !counter before Ref.modify (Fn.curry (op +) 1) counter

    val eq = (op =)
    val compare = Int.compare
  end

structure Type =
  struct
    datatype t =
      Unit
    | Prod of t * t
    | Arrow of t * t
    | Answer
  end

structure Term =
  struct
    datatype t =
      Var of Variable.t
    | Triv
    | Pair of t * t
    | Fst of t
    | Snd of t
    | Lam of Variable.t * t
    | App of t * t
    | Result of bool
  end

structure Normal =
  struct
    datatype normal =
      Neutral of neutral
    | Triv
    | Pair of normal * normal
    | Lam of Variable.t * normal

    and neutral =
      Var of Variable.t
    | Fst of neutral
    | Snd of neutral
    | App of neutral * normal
    | Result of bool

    fun subst (t : Term.t) (x : Variable.t) : normal -> Term.t =
      fn Neutral u     => subst' t x u
       | Triv          => Term.Triv
       | Pair (n1, n2) => Term.Pair (subst t x n1, subst t x n2)
       | Lam (y, n1)   => Term.Lam (y, subst (if Variable.eq (x, y) then Term.Var y else t) x n1)
    and subst' (t : Term.t) (x : Variable.t) : neutral -> Term.t =
      fn Var y       => if Variable.eq (x, y) then t else Term.Var y
       | Fst u       => Term.Fst (subst' t x u)
       | Snd u       => Term.Snd (subst' t x u)
       | App (u, n1) => Term.App (subst' t x u, subst t x n1)
       | Result b    => Term.Result b

    fun toTerm (n : normal) : Term.t =
      case n of
        Neutral u     => toTerm' u
      | Triv          => Term.Triv
      | Pair (n1, n2) => Term.Pair (toTerm n1, toTerm n2)
      | Lam (x, n1)   => Term.Lam (x, toTerm n1)
    and toTerm' (u : neutral) : Term.t =
      case u of
        Var x       => Term.Var x
      | Fst u       => Term.Fst (toTerm' u)
      | Snd u       => Term.Snd (toTerm' u)
      | App (u, n1) => Term.App (toTerm' u, toTerm n1)
      | Result b    => Term.Result b
  end

exception TypeError


fun norm (m : Term.t) : Normal.normal =
  case m of
    Term.Var x         => Normal.Neutral (Normal.Var x)
  | Term.Triv          => Normal.Triv
  | Term.Pair (m1, m2) => Normal.Pair (norm m1, norm m2)
  | Term.Fst m         => (
      case norm m of
        Normal.Neutral u     => Normal.Neutral (Normal.Fst u)
      | Normal.Pair (n1, n2) => n1
      | _                    => raise TypeError
    )
  | Term.Snd m         => (
      case norm m of
        Normal.Neutral u     => Normal.Neutral (Normal.Fst u)
      | Normal.Pair (n1, n2) => n2
      | _                    => raise TypeError
    )
  | Term.Lam (x, m)    => Normal.Lam (x, norm m)
  | Term.App (m1, m2)  => (
      case norm m1 of
        Normal.Neutral u  => Normal.Neutral (Normal.App (u, norm m2))
      | Normal.Lam (x, n) => norm (Normal.subst m2 x n)
      | _                 => raise TypeError
    )
  | Term.Result b         => Normal.Neutral (Normal.Result b)


structure Ctx = DictFun (RedBlackDict (structure Key = Variable))
type ctx = Type.t Ctx.dict

val return = SOME

infixr 0 >>=
fun x >>= f = Option.mapPartial f x

infixr 0 >>
fun f >> g = g o f

fun check (ctx : ctx) (m : Term.t) (m' : Term.t) (a : Type.t) : unit option =
  case a of
    Type.Unit => return ()
  | Type.Prod (a1, a2) =>
      check ctx (Term.Fst m) (Term.Fst m') a1 >>= (fn () =>
        check ctx (Term.Snd m) (Term.Snd m') a2 >>= (fn () =>
          return ()
        )
      )
  | Type.Arrow (a1, a2) =>
      let
        val x = Variable.new ()
      in
        check
          (Ctx.insert ctx x a1)
          (Term.App (m, Term.Var x))
          (Term.App (m', Term.Var x))
          a2
      end
  | Type.Answer => (
      case (norm m, norm m') of
        (Normal.Neutral u, Normal.Neutral u') =>
          infer ctx u u' >>= (ignore >> return)
      | _ => raise TypeError
    )

and infer (ctx : ctx) (u : Normal.neutral) (u' : Normal.neutral) : Type.t option =
  case (u, u') of
    (Normal.Var x, Normal.Var x') =>
      if Variable.eq (x, x')
        then return (Ctx.lookup ctx x)
        else NONE
  | (Normal.Fst u, Normal.Fst u') => infer ctx u u' >>= (
      fn Type.Prod (a1, _) => return a1
       | _                 => raise TypeError
    )
  | (Normal.Snd u, Normal.Snd u') => infer ctx u u' >>= (
      fn Type.Prod (_, a2) => return a2
       | _                 => raise TypeError
    )
  | (Normal.App (u, m), Normal.App (u', m')) => infer ctx u u' >>= (
      fn Type.Arrow (a1, a2) =>
          check ctx (Normal.toTerm m) (Normal.toTerm m') a1 >>= (fn () =>
            return a2
          )
       | _                   => raise TypeError
    )
  | (Normal.Result b, Normal.Result b') =>
      if b = b'
        then return Type.Answer
        else NONE
  | _ => NONE

val demo =
  let
    open Type Term
    val x = Variable.new ()
  in
    check
      Ctx.empty
      (Lam (x, Var x))
      (Lam (x, Triv))
      (Arrow (Unit, Unit))
  end

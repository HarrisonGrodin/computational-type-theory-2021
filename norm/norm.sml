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

    fun toTerm (n : normal) : Term.t =
      case n of
        Neutral u     => toTerm' u
      | Triv          => Term.Triv
      | Pair (n1, n2) => Term.Pair (toTerm n1, toTerm n2)
      | Lam (x, n)    => Term.Lam (x, toTerm n)
    and toTerm' (u : neutral) : Term.t =
      case u of
        Var x      => Term.Var x
      | Fst u      => Term.Fst (toTerm' u)
      | Snd u      => Term.Snd (toTerm' u)
      | App (u, n) => Term.App (toTerm' u, toTerm n)

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
  end

exception TypeError

fun norm (term : Term.t) : Normal.normal =
  case term of
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

val demo =
  let
    open Term
    val x = Variable.new ()
    val y = Variable.new ()
  in
    norm (Fst (App (Lam (x, Pair (Var x, Triv)), Var y)))
  end

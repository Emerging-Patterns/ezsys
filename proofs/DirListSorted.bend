# proofs of laws/DirListSorted.bend
import Base
import ../src/dir.bend as Dir
import ../laws/DirListSorted.bend as Laws
import ./lemmas/BoolFacts.bend as M1

# --- order facts ---

# a comparison seen from the other side
def cflip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# two bits compared the other way round give the flipped answer
law bool_cmp_flip:
  for a: Bool
  for b: Bool
  {Bool.cmp(b, a) == cflip(Bool.cmp(a, b)) : Cmp}

def bool_cmp_flip(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# the last step of a word comparison, flipped
law fin_flip:
  for +ab: Bool
  for +bb: Bool
  for t: Cmp
  {Word.cmp.fin(bb, ab, cflip(t)) == cflip(Word.cmp.fin(ab, bb, t)) : Cmp}

def fin_flip(ab, bb, t):
  match t:
    case LT{}:
      {==}
    case EQ{}:
      bool_cmp_flip(ab, bb)
    case GT{}:
      {==}

# two words compared the other way round give the flipped answer
law word_cmp_flip:
  for n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, b, a) == cflip(Word.cmp(n, a, b)) : Cmp}

def word_cmp_flip(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, bt, at), cflip(Word.cmp(p, at, bt)),
            word_cmp_flip(p, at, bt))
            : {Word.cmp.fin(bb, ab, _) == cflip(Word.cmp.fin(ab, bb,
              Word.cmp(p, at, bt))) : Cmp}
          fin_flip(ab, bb, Word.cmp(p, at, bt))

# two numbers compared the other way round give the flipped answer
law u32_cmp_flip:
  for +x: U32
  for +y: U32
  {U32.cmp(y, x) == cflip(U32.cmp(x, y)) : Cmp}

def u32_cmp_flip(x, y):
  match x y:
    case U32{+a} U32{+b}:
      word_cmp_flip(32n, a, b)

# two texts compared the other way round give the flipped answer
law order_flip:
  for +a: String
  for +b: String
  for +c: Cmp
  {String.order.go(b, a, cflip(c)) == cflip(String.order.go(a, b, c)) : Cmp}

def order_flip(a, b, c):
  match a b:
    case SNil{} SNil{}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SNil{} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SCon{Chr{+x}, +t1} SNil{}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          %Equal.sym(Cmp, U32.cmp(y, x), cflip(U32.cmp(x, y)),
            u32_cmp_flip(x, y))
            : {String.order.go(t2, t1, _)
              == cflip(String.order.go(t1, t2, U32.cmp(x, y))) : Cmp}
          order_flip(t1, t2, U32.cmp(x, y))
        case GT{}:
          {==}

# a comparison that is not at most is at least, the other way round
law le_flip:
  for c: Cmp
  for e: {Cmp.is_le(c) == False{} : Bool}
  {Cmp.is_le(cflip(c)) == True{} : Bool}

def le_flip(c, e):
  match c:
    case LT{}:
      M1.gone(&1, {False{} == True{} : Bool}, M1.clash(e))
    case EQ{}:
      M1.gone(&1, {True{} == True{} : Bool}, M1.clash(e))
    case GT{}:
      {==}

# String.order is total: a text not at most another is at least it
law le_total:
  for +x: String
  for +y: String
  for e: {String.is_le(x, y) == False{} : Bool}
  {String.is_le(y, x) == True{} : Bool}

def le_total(x, y, e):
  %Equal.sym(Cmp, String.order.go(y, x, EQ{}),
    cflip(String.order.go(x, y, EQ{})), order_flip(x, y, EQ{}))
    : {Cmp.is_le(_) == True{} : Bool}
  le_flip(String.order.go(x, y, EQ{}), e)

# --- sorting names ---

# a true and has a true first test
law and_true_l:
  for a: Bool
  for b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_true_l(a, _b, e):
  match a:
    case False{}:
      M1.gone(&1, {False{} == True{} : Bool},
        M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{}:
      {==}

# a true and has a true second test
law and_true_r:
  for a: Bool
  for b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_true_r(a, b, e):
  match a:
    case False{}:
      M1.gone(&1, {b == True{} : Bool}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{}:
      e

# a name put into the names after prev, no less than prev, keeps them
# ascending from prev
def insert_from.goal(
  xs: List<&2, String>,
  +prev: String,
  +x: String
) -> Type:
  {Laws.ascending.from(Dir.dir.insert(x, xs), prev) == True{} : Bool}

law insert_from:
  for +xs: List<&2, String>
  for +prev: String
  for +x: String
  for e1: {String.is_le(prev, x) == True{} : Bool}
  for +e2: {Laws.ascending.from(xs, prev) == True{} : Bool}
  insert_from.goal(xs, prev, x)

def insert_from.at(
  +prev: String,
  +x: String,
  +y: String,
  +ys: List<&2, String>,
  b: Bool,
  +eb: {String.is_le(x, y) == b : Bool},
  e1: {String.is_le(prev, x) == True{} : Bool},
  p1: {String.is_le(prev, y) == True{} : Bool},
  p2: {Laws.ascending.from(ys, y) == True{} : Bool},
  ih: {String.is_le(y, x) == True{} : Bool} -> insert_from.goal(ys, y, x)
) -> insert_from.goal(Con{y, ys}, prev, x):
  match b:
    case True{}:
      %Equal.sym(Bool, String.is_le(x, y), True{}, eb)
        : {Laws.ascending.from(Dir.dir.insert.pick(_, x, y, ys,
          _u => Dir.dir.insert(x, ys)), prev) == True{} : Bool}
      %Equal.sym(Bool, String.is_le(x, y), True{}, eb)
        : {Bool.and(String.is_le(prev, x),
          Bool.and(_, Laws.ascending.from(ys, y))) == True{} : Bool}
      %Equal.sym(Bool, String.is_le(prev, x), True{}, e1)
        : {Bool.and(_, Laws.ascending.from(ys, y)) == True{} : Bool}
      p2
    case False{}:
      %Equal.sym(Bool, String.is_le(x, y), False{}, eb)
        : {Laws.ascending.from(Dir.dir.insert.pick(_, x, y, ys,
          _u => Dir.dir.insert(x, ys)), prev) == True{} : Bool}
      %Equal.sym(Bool, String.is_le(prev, y), True{}, p1)
        : {Bool.and(_, Laws.ascending.from(Dir.dir.insert(x, ys), y))
          == True{} : Bool}
      ih(le_total(x, y, eb))

def insert_from(xs, prev, x, e1, e2):
  match xs:
    case Nil{}:
      %Equal.sym(Bool, String.is_le(prev, x), True{}, e1)
        : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Con{+y, +ys}:
      insert_from.at(prev, x, y, ys, String.is_le(x, y), {==}, e1,
        and_true_l(String.is_le(prev, y), Laws.ascending.from(ys, y), e2),
        and_true_r(String.is_le(prev, y), Laws.ascending.from(ys, y), e2),
        h => insert_from(ys, y, x, h,
          and_true_r(String.is_le(prev, y), Laws.ascending.from(ys, y), e2)))

# a name put into ascending names keeps them ascending
law asc_insert:
  for +xs: List<&2, String>
  for +x: String
  for +e: {Laws.ascending(xs) == True{} : Bool}
  {Laws.ascending(Dir.dir.insert(x, xs)) == True{} : Bool}

def asc_insert.at(
  +x: String,
  +y: String,
  +ys: List<&2, String>,
  b: Bool,
  +eb: {String.is_le(x, y) == b : Bool},
  e: {Laws.ascending.from(ys, y) == True{} : Bool}
) -> {Laws.ascending(Dir.dir.insert(x, Con{y, ys})) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, String.is_le(x, y), True{}, eb)
        : {Laws.ascending(Dir.dir.insert.pick(_, x, y, ys,
          _u => Dir.dir.insert(x, ys))) == True{} : Bool}
      %Equal.sym(Bool, String.is_le(x, y), True{}, eb)
        : {Bool.and(_, Laws.ascending.from(ys, y)) == True{} : Bool}
      e
    case False{}:
      %Equal.sym(Bool, String.is_le(x, y), False{}, eb)
        : {Laws.ascending(Dir.dir.insert.pick(_, x, y, ys,
          _u => Dir.dir.insert(x, ys))) == True{} : Bool}
      insert_from(ys, y, x, le_total(x, y, eb), e)

def asc_insert(xs, x, e):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +ys}:
      asc_insert.at(x, y, ys, String.is_le(x, y), {==}, e)

# sorted names are ascending
law asc_sort:
  for +xs: List<&2, String>
  {Laws.ascending(Dir.dir.sort(xs)) == True{} : Bool}

def asc_sort(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      asc_insert(Dir.dir.sort(xt), x, asc_sort(xt))

def Laws.dir_sorted(raw):
  asc_sort(Dir.dir.keep(raw))

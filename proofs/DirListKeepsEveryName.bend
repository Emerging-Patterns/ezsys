# proofs of laws/DirListKeepsEveryName.bend
import Base
import ../src/dir.bend as Dir
import ../laws/DirListKeepsEveryName.bend as Laws
import ./lemmas/BoolFacts.bend as M1

# --- equal texts ---

# bits that compare equal are equal
law bool_cmp_eq:
  for a: Bool
  for b: Bool
  for e: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}
  {a == b : Bool}

def bool_cmp_eq(a, b, e):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      M1.gone(&1, {False{} == True{} : Bool}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{} False{}:
      M1.gone(&1, {True{} == False{} : Bool}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{} True{}:
      {==}

# a word comparison that ends equal had equal rest
law fin_eq_t:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}
  {Cmp.is_eq(t) == True{} : Bool}

def fin_eq_t(_ab, _bb, t, e):
  match t:
    case LT{}:
      M1.gone(&1, {False{} == True{} : Bool}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case EQ{}:
      {==}
    case GT{}:
      M1.gone(&1, {False{} == True{} : Bool}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))

# a word comparison that ends equal had equal first bits
law fin_eq_h:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}
  {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool}

def fin_eq_h(ab, bb, t, e):
  match t:
    case LT{}:
      M1.gone(&1, {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool},
        M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case EQ{}:
      e
    case GT{}:
      M1.gone(&1, {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool},
        M1.clash(Equal.sym(Bool, False{}, True{}, e)))

# words that compare equal are equal
law word_cmp_eq:
  for n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def word_cmp_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %bool_cmp_eq(ab, bb, fin_eq_h(ab, bb, Word.cmp(p, at, bt), e))
            : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          Equal.cong(Word(p), Word(1n+p), w => WCon{ab, w}, at, bt,
            word_cmp_eq(p, at, bt, fin_eq_t(ab, bb, Word.cmp(p, at, bt), e)))

# numbers that compare equal are equal
law u32_cmp_eq:
  for +x: U32
  for +y: U32
  for e: {Cmp.is_eq(U32.cmp(x, y)) == True{} : Bool}
  {x == y : U32}

def u32_cmp_eq(x, y, e):
  match x y:
    case U32{+a} U32{+b}:
      Equal.cong(Word(32n), U32, w => U32{w}, a, b, word_cmp_eq(32n, a, b, e))

# a text comparison that ends equal started equal
law order_eq_c:
  for +a: String
  for +b: String
  for +c: Cmp
  for e: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}
  {Cmp.is_eq(c) == True{} : Bool}

def order_eq_c(a, b, c, e):
  match a b:
    case SNil{} SNil{}:
      e
    case SNil{} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          e
        case EQ{}:
          {==}
        case GT{}:
          e
    case SCon{Chr{+x}, +t1} SNil{}:
      match c:
        case LT{}:
          e
        case EQ{}:
          {==}
        case GT{}:
          e
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          e
        case EQ{}:
          {==}
        case GT{}:
          e

# texts whose comparison ends equal are equal
law order_eq:
  for +a: String
  for +b: String
  for +c: Cmp
  for +e: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}
  {a == b : String}

def order_eq(a, b, c, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          M1.gone(&1, {SNil{} == SCon{Chr{y}, t2} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
        case EQ{}:
          M1.gone(&1, {SNil{} == SCon{Chr{y}, t2} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
        case GT{}:
          M1.gone(&1, {SNil{} == SCon{Chr{y}, t2} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case SCon{Chr{+x}, +t1} SNil{}:
      match c:
        case LT{}:
          M1.gone(&1, {SCon{Chr{x}, t1} == SNil{} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
        case EQ{}:
          M1.gone(&1, {SCon{Chr{x}, t1} == SNil{} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
        case GT{}:
          M1.gone(&1, {SCon{Chr{x}, t1} == SNil{} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          M1.gone(&1, {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))
        case EQ{}:
          %u32_cmp_eq(x, y, order_eq_c(t1, t2, U32.cmp(x, y), e))
            : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
          Equal.cong(String, String, s => SCon{Chr{x}, s}, t1, t2,
            order_eq(t1, t2, U32.cmp(x, y), e))
        case GT{}:
          M1.gone(&1, {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, M1.clash(Equal.sym(Bool, False{}, True{}, e)))

# texts String.eq calls equal are equal
law eq_sound:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def eq_sound(a, b, e):
  order_eq(a, b, EQ{}, e)

# --- counting names ---

# two copies-when picks commute
law pick_swap:
  for a: Bool
  for b: Bool
  for +m: Nat
  {Laws.listed.pick(a, Laws.listed.pick(b, m))
    == Laws.listed.pick(b, Laws.listed.pick(a, m)) : Nat}

def pick_swap(a, b, _m):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# a pick between two equal numbers is that number
law pick_same:
  for c: Bool
  for +m: Nat
  {Bool.pick(Nat, c, m, m) == m : Nat}

def pick_same(c, _m):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

# inserting a name counts it once more when it is the name counted
def insert_count.goal(
  xs: List<&2, String>,
  +x: String,
  +name: String
) -> Type:
  {Laws.listed(name, Dir.dir.insert(x, xs))
    == Laws.listed.pick(String.eq(x, name), Laws.listed(name, xs)) : Nat}

law insert_count:
  for xs: List<&2, String>
  for +x: String
  for +name: String
  insert_count.goal(xs, x, name)

def insert_count.at(
  +x: String,
  +y: String,
  +ys: List<&2, String>,
  +name: String,
  b: Bool,
  e: {String.is_le(x, y) == b : Bool},
  ih: insert_count.goal(ys, x, name)
) -> insert_count.goal(Con{y, ys}, x, name):
  match b:
    case True{}:
      %Equal.sym(Bool, String.is_le(x, y), b, e)
        : {Laws.listed(name, Dir.dir.insert.pick(_, x, y, ys,
        _u => Dir.dir.insert(x, ys)))
        == Laws.listed.pick(String.eq(x, name), Laws.listed(name, Con{y, ys}))
        : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, String.is_le(x, y), b, e)
        : {Laws.listed(name, Dir.dir.insert.pick(_, x, y, ys,
        _u => Dir.dir.insert(x, ys)))
        == Laws.listed.pick(String.eq(x, name), Laws.listed(name, Con{y, ys}))
        : Nat}
      %Equal.sym(Nat, Laws.listed(name, Dir.dir.insert(x, ys)),
        Laws.listed.pick(String.eq(x, name), Laws.listed(name, ys)), ih)
        : {Laws.listed.pick(String.eq(y, name), _)
        == Laws.listed.pick(String.eq(x, name),
          Laws.listed.pick(String.eq(y, name), Laws.listed(name, ys))) : Nat}
      pick_swap(String.eq(y, name), String.eq(x, name), Laws.listed(name, ys))

def insert_count(xs, x, name):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +ys}:
      insert_count.at(x, y, ys, name, String.is_le(x, y), {==},
        insert_count(ys, x, name))

# sorting keeps every name's count
law sort_count:
  for xs: List<&2, String>
  for +name: String
  {Laws.listed(name, Dir.dir.sort(xs)) == Laws.listed(name, xs) : Nat}

def sort_count(xs, name):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      %Equal.sym(Nat, Laws.listed(name, Dir.dir.insert(x, Dir.dir.sort(xt))),
        Laws.listed.pick(String.eq(x, name), Laws.listed(name, Dir.dir.sort(xt))),
        insert_count(Dir.dir.sort(xt), x, name))
        : {_ == Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt)) : Nat}
      Equal.cong(Nat, Nat, m => Laws.listed.pick(String.eq(x, name), m),
        Laws.listed(name, Dir.dir.sort(xt)), Laws.listed(name, xt),
        sort_count(xt, name))

# equal names are both dots or neither
law dot_same:
  for +x: String
  for +name: String
  for e: {String.eq(x, name) == True{} : Bool}
  {Dir.dir.dot(x) == Dir.dir.dot(name) : Bool}

def dot_same(x, name, e):
  Equal.cong(String, Bool, +s => Dir.dir.dot(s), x, name, eq_sound(x, name, e))

# what keeping the names does to a name's count
def keep_count.goal(+xs: List<&2, String>, +name: String) -> Type:
  {Laws.listed(name, Dir.dir.keep(xs))
    == Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xs)) : Nat}

# the count of a kept name, by whether the first raw name is a dot (d) and
# is the name (h), given the count for the rest (ih)
def keep_count.at(
  +x: String,
  +xt: List<&2, String>,
  +name: String,
  d: Bool,
  +ed: {Dir.dir.dot(x) == d : Bool},
  h: Bool,
  +eh: {String.eq(x, name) == h : Bool},
  ih: keep_count.goal(xt, name)
) -> keep_count.goal(Con{x, xt}, name):
  match d h:
    case True{} True{}:
      %Equal.sym(Bool, Dir.dir.dot(x), d, ed)
        : {Laws.listed(name, Dir.dir.keep.pick(_, x, _u => Dir.dir.keep(xt)))
        == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.sym(Nat, Laws.listed(name, Dir.dir.keep(xt)),
        Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xt)), ih)
        : {_ == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.trans(Bool, True{}, Dir.dir.dot(x), Dir.dir.dot(name),
        Equal.sym(Bool, Dir.dir.dot(x), True{}, ed), dot_same(x, name, eh))
        : {Bool.pick(Nat, _, 0n, Laws.listed(name, xt))
          == Bool.pick(Nat, _, 0n,
            Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, Dir.dir.dot(x), d, ed)
        : {Laws.listed(name, Dir.dir.keep.pick(_, x, _u => Dir.dir.keep(xt)))
        == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.sym(Nat, Laws.listed(name, Dir.dir.keep(xt)),
        Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xt)), ih)
        : {_ == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.sym(Bool, String.eq(x, name), h, eh)
        : {Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xt))
        == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(_, Laws.listed(name, xt))) : Nat}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Dir.dir.dot(x), d, ed)
        : {Laws.listed(name, Dir.dir.keep.pick(_, x, _u => Dir.dir.keep(xt)))
        == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.sym(Nat, Laws.listed(name, Dir.dir.keep(xt)),
        Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xt)), ih)
        : {Laws.listed.pick(String.eq(x, name), _)
          == Bool.pick(Nat, Dir.dir.dot(name), 0n,
            Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.sym(Bool, String.eq(x, name), h, eh)
        : {Laws.listed.pick(_,
        Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xt)))
        == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(_, Laws.listed(name, xt))) : Nat}
      %Equal.trans(Bool, False{}, Dir.dir.dot(x), Dir.dir.dot(name),
        Equal.sym(Bool, Dir.dir.dot(x), False{}, ed), dot_same(x, name, eh))
        : {Laws.listed.pick(True{}, Bool.pick(Nat, _, 0n, Laws.listed(name, xt)))
          == Bool.pick(Nat, _, 0n,
            Laws.listed.pick(True{}, Laws.listed(name, xt))) : Nat}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Dir.dir.dot(x), d, ed)
        : {Laws.listed(name, Dir.dir.keep.pick(_, x, _u => Dir.dir.keep(xt)))
        == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.sym(Nat, Laws.listed(name, Dir.dir.keep(xt)),
        Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xt)), ih)
        : {Laws.listed.pick(String.eq(x, name), _)
          == Bool.pick(Nat, Dir.dir.dot(name), 0n,
            Laws.listed.pick(String.eq(x, name), Laws.listed(name, xt))) : Nat}
      %Equal.sym(Bool, String.eq(x, name), h, eh)
        : {Laws.listed.pick(_,
        Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, xt)))
        == Bool.pick(Nat, Dir.dir.dot(name), 0n,
          Laws.listed.pick(_, Laws.listed(name, xt))) : Nat}
      {==}

# keeping counts a name as the raw names do, and a dot never
law keep_count:
  for xs: List<&2, String>
  for +name: String
  keep_count.goal(xs, name)

def keep_count(xs, name):
  match xs:
    case Nil{}:
      Equal.sym(Nat, Bool.pick(Nat, Dir.dir.dot(name), 0n, 0n), 0n,
        pick_same(Dir.dir.dot(name), 0n))
    case Con{+x, +xt}:
      keep_count.at(x, xt, name, Dir.dir.dot(x), {==}, String.eq(x, name), {==},
        keep_count(xt, name))

def Laws.dir_count(raw, name):
  Equal.trans(Nat, Laws.listed(name, Dir.dir.sort(Dir.dir.keep(raw))),
    Laws.listed(name, Dir.dir.keep(raw)),
    Bool.pick(Nat, Dir.dir.dot(name), 0n, Laws.listed(name, raw)),
    sort_count(Dir.dir.keep(raw), name), keep_count(raw, name))

# proofs of laws/ReprQuotesAndEscapes.bend
import Base
import ../src/errno.bend as Err
import ../laws/ReprQuotesAndEscapes.bend as Laws

def Laws.repr_shape(_path):
  {==}

def Laws.quote_double(path, one, two):
  %Equal.sym(Bool, String.contains(path, "'"), True{}, one)
    : {Err.err.quote.pick(Bool.and(_,
      Bool.not(String.contains(path, "\"")))) == '"' : Char}
  %Equal.sym(Bool, String.contains(path, "\""), False{}, two)
    : {Err.err.quote.pick(Bool.not(_)) == '"' : Char}
  {==}

def Laws.quote_plain(path, e):
  %Equal.sym(Bool, String.contains(path, "'"), False{}, e)
    : {Err.err.quote.pick(Bool.and(_,
      Bool.not(String.contains(path, "\"")))) == '\'' : Char}
  {==}

# and of anything with false is false
law and_false:
  for a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.quote_both(path, e):
  %Equal.sym(Bool, String.contains(path, "\""), True{}, e)
    : {Err.err.quote.pick(Bool.and(String.contains(path, "'"), Bool.not(_)))
      == '\'' : Char}
  %Equal.sym(Bool, Bool.and(String.contains(path, "'"), False{}), False{},
    and_false(String.contains(path, "'")))
    : {Err.err.quote.pick(_) == '\'' : Char}
  {==}

def Laws.go_empty(_q):
  {==}

def Laws.go_char(_q, _c, _t):
  {==}

def Laws.esc_tab(_q):
  {==}

def Laws.esc_newline(_q):
  {==}

def Laws.esc_return(_q):
  {==}

def Laws.esc_backslash(_q):
  {==}

def Laws.hex_pair(_x):
  {==}

def Laws.esc_hex(q, x, set, tab, nl, cr):
  %Equal.sym(Bool, Err.err.hexed(x), True{}, set)
    : {Err.err.when(_, _u => Err.err.ctl(x), _u => Err.err.plain(q, x))
      == "\\x" ++ Err.err.hex2(x) : String}
  %Equal.sym(Bool, U32.is_eq(x, 9), False{}, tab)
    : {Err.err.when(_, _u => "\\t",
      _u => Err.err.when(U32.is_eq(x, 10), _v => "\\n",
        _v => Err.err.when(U32.is_eq(x, 13), _w => "\\r",
          _w => "\\x" ++ Err.err.hex2(x))))
      == "\\x" ++ Err.err.hex2(x) : String}
  %Equal.sym(Bool, U32.is_eq(x, 10), False{}, nl)
    : {Err.err.when(_, _v => "\\n",
      _v => Err.err.when(U32.is_eq(x, 13), _w => "\\r",
        _w => "\\x" ++ Err.err.hex2(x)))
      == "\\x" ++ Err.err.hex2(x) : String}
  %Equal.sym(Bool, U32.is_eq(x, 13), False{}, cr)
    : {Err.err.when(_, _w => "\\r", _w => "\\x" ++ Err.err.hex2(x))
      == "\\x" ++ Err.err.hex2(x) : String}
  {==}

def Laws.esc_quote(q, x, set, bs, hit):
  %Equal.sym(Bool, Err.err.hexed(x), False{}, set)
    : {Err.err.when(_, _u => Err.err.ctl(x), _u => Err.err.plain(q, x))
      == SCon{'\\', SCon{q, SNil{}}} : String}
  %Equal.sym(Bool, U32.is_eq(x, 92), False{}, bs)
    : {Err.err.when(_, _u => "\\\\",
      _u => Err.err.when(Char.is_eq(Chr{x}, q),
        _v => SCon{'\\', SCon{q, SNil{}}}, _v => SCon{Chr{x}, SNil{}}))
      == SCon{'\\', SCon{q, SNil{}}} : String}
  %Equal.sym(Bool, Char.is_eq(Chr{x}, q), True{}, hit)
    : {Err.err.when(_, _v => SCon{'\\', SCon{q, SNil{}}},
      _v => SCon{Chr{x}, SNil{}}) == SCon{'\\', SCon{q, SNil{}}} : String}
  {==}

def Laws.esc_plain(q, x, set, bs, miss):
  %Equal.sym(Bool, Err.err.hexed(x), False{}, set)
    : {Err.err.when(_, _u => Err.err.ctl(x), _u => Err.err.plain(q, x))
      == SCon{Chr{x}, SNil{}} : String}
  %Equal.sym(Bool, U32.is_eq(x, 92), False{}, bs)
    : {Err.err.when(_, _u => "\\\\",
      _u => Err.err.when(Char.is_eq(Chr{x}, q),
        _v => SCon{'\\', SCon{q, SNil{}}}, _v => SCon{Chr{x}, SNil{}}))
      == SCon{Chr{x}, SNil{}} : String}
  %Equal.sym(Bool, Char.is_eq(Chr{x}, q), False{}, miss)
    : {Err.err.when(_, _v => SCon{'\\', SCon{q, SNil{}}},
      _v => SCon{Chr{x}, SNil{}}) == SCon{Chr{x}, SNil{}} : String}
  {==}

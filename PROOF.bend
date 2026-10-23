# ezsys: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./src/step.bend as Step
import ./src/clock.bend as Clock
import ./src/text.bend as Text
import ./src/dir.bend as Dir
import ./src/errno.bend as Err
import ./src/str.bend as Str
import ./LAWS.bend as Laws

# --- Bool facts ---

# Unit for True, Empty for False: tells them apart
def bit(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
def clash(e: {True{} == False{} : Bool}) -> Empty:
  %e : bit(_)
  Unit{}

# anything follows from Empty
def gone(a, -A: Kind(a), e: Empty) -> A:
  match e:

# a false any has a false first test
law any_false_l:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.any(here, rest) == False{} : Bool}
  {here == False{} : Bool}

def any_false_l(here, _rest, e):
  match here:
    case False{}:
      {==}
    case True{}:
      gone(&1, {True{} == False{} : Bool}, clash(e))

# a false any has a false rest
law any_false_r:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.any(here, rest) == False{} : Bool}
  {rest(Unit{}) == False{} : Bool}

def any_false_r(here, rest, e):
  match here:
    case False{}:
      e
    case True{}:
      gone(&1, {rest(Unit{}) == False{} : Bool}, clash(e))

# not of a true is false
law not_true:
  for a: Bool
  for e: {Bool.not(a) == True{} : Bool}
  {a == False{} : Bool}

def not_true(a, e):
  match a:
    case False{}:
      {==}
    case True{}:
      gone(&1, {True{} == False{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))

# a true all has a true first test
law all_true_l:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.all(here, rest) == True{} : Bool}
  {here == True{} : Bool}

def all_true_l(here, _rest, e):
  match here:
    case False{}:
      gone(&1, {False{} == True{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{}:
      {==}

# a true all has a true rest
law all_true_r:
  for here: Bool
  for rest: Unit -> Bool
  for e: {Text.text.all(here, rest) == True{} : Bool}
  {rest(Unit{}) == True{} : Bool}

def all_true_r(here, rest, e):
  match here:
    case False{}:
      gone(&1, {rest(Unit{}) == True{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{}:
      e

# --- Char and String facts ---

def eq.bool_cmp_self(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def eq.word_cmp_self(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)),
            Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(b, b, c),
              Word.cmp(p, t, t), EQ{}, eq.word_cmp_self(p, t)),
            eq.bool_cmp_self(b))

def eq.u32_cmp_self(u: U32) -> {U32.cmp(u, u) == EQ{} : Cmp}:
  match u:
    case U32{+w}:
      eq.word_cmp_self(32n, w)

def eq.char_eq_self(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{+x}:
      Equal.cong(Cmp, Bool, r => Cmp.is_eq(r), U32.cmp(x, x), EQ{},
        eq.u32_cmp_self(x))

# a text starts with itself, whatever follows it
law starts_self:
  for +s: String
  for +x: String
  {String.starts_with(s ++ x, s) == True{} : Bool}

def starts_self(s, x):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, eq.char_eq_self(c))
        : {String.starts_with.go.if(t, t ++ x, _) == True{} : Bool}
      starts_self(t, x)

# appending nothing changes nothing
law app_nil:
  for +a: String
  {a ++ "" == a : String}

def app_nil(a):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{h, x}, t ++ "", t, app_nil(t))

# appending is associative
law app_assoc:
  for +a: String
  for +b: String
  for +c: String
  {(a ++ b) ++ c == a ++ (b ++ c) : String}

def app_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{h, x}, (t ++ b) ++ c, t ++ (b ++ c),
        app_assoc(t, b, c))

# --- files and environment ---

def Laws.read_fail(_code, _why, _got):
  {==}

def Laws.read_end(_got):
  {==}

def Laws.read_more(_h, _t, _got):
  {==}

def Laws.save_tmp(_path):
  {==}

def Laws.save_fail(_code, _why):
  {==}

def Laws.save_move(_u):
  {==}

def Laws.env_set(_value, _fallback):
  {==}

def Laws.env_unset(_code, _why, _fallback):
  {==}

# --- wall clock ---

def Laws.iso_width(_secs, _ms):
  {==}

def Laws.iso_split(_secs, _ms):
  {==}

def Laws.clock_fields(_sod, _ms):
  {==}

def Laws.date_fields(_days):
  {==}

def Laws.last_second(_ms):
  {==}

# --- weekdays and ISO weeks ---

def Laws.weekday_epoch(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 0, e)
    : {Clock.time.weekday(_) == 4 : U32}
  {==}

# a day on, then the rest, is the rest, then a day on
law wd_go_next:
  for +num: Nat
  for +day: Clock.Wd
  {Clock.time.wd.go(num, Clock.time.wd.next(day)) == Clock.time.wd.next(Clock.time.wd.go(num, day)) : Clock.Wd}

def wd_go_next(num, day):
  match num:
    case 0n:
      {==}
    case 1n+more:
      wd_go_next(more, Clock.time.wd.next(day))

def Laws.weekday_step(num):
  wd_go_next(num, Clock.Thu{})

def Laws.weekday_next(day):
  match day:
    case Clock.Mon{}:
      {==}
    case Clock.Tue{}:
      {==}
    case Clock.Wed{}:
      {==}
    case Clock.Thu{}:
      {==}
    case Clock.Fri{}:
      {==}
    case Clock.Sat{}:
      {==}
    case Clock.Sun{}:
      {==}

def Laws.weekday_nat(_num):
  {==}

# Monday is the offset 0
law plus_mon:
  for day: Clock.Wd
  {Clock.time.wd.plus(day, Clock.Mon{}) == day : Clock.Wd}

def plus_mon(day):
  match day:
    case Clock.Mon{}:
      {==}
    case Clock.Tue{}:
      {==}
    case Clock.Wed{}:
      {==}
    case Clock.Thu{}:
      {==}
    case Clock.Fri{}:
      {==}
    case Clock.Sat{}:
      {==}
    case Clock.Sun{}:
      {==}

# a Tuesday's offset is a day on
law plus_tue:
  for day: Clock.Wd
  {Clock.time.wd.plus(Clock.Tue{}, day) == Clock.time.wd.next(day) : Clock.Wd}

def plus_tue(day):
  match day:
    case Clock.Mon{}:
      {==}
    case Clock.Tue{}:
      {==}
    case Clock.Wed{}:
      {==}
    case Clock.Thu{}:
      {==}
    case Clock.Fri{}:
      {==}
    case Clock.Sat{}:
      {==}
    case Clock.Sun{}:
      {==}

# a day on before an offset is a day on after it
law plus_step:
  for +day: Clock.Wd
  for +off: Clock.Wd
  {Clock.time.wd.plus(Clock.time.wd.next(day), off) == Clock.time.wd.plus(day, Clock.time.wd.plus(Clock.Tue{}, off))
    : Clock.Wd}

def plus_step(day, off):
  match day:
    case Clock.Mon{}:
      match off:
        case Clock.Mon{}:
          {==}
        case Clock.Tue{}:
          {==}
        case Clock.Wed{}:
          {==}
        case Clock.Thu{}:
          {==}
        case Clock.Fri{}:
          {==}
        case Clock.Sat{}:
          {==}
        case Clock.Sun{}:
          {==}
    case Clock.Tue{}:
      match off:
        case Clock.Mon{}:
          {==}
        case Clock.Tue{}:
          {==}
        case Clock.Wed{}:
          {==}
        case Clock.Thu{}:
          {==}
        case Clock.Fri{}:
          {==}
        case Clock.Sat{}:
          {==}
        case Clock.Sun{}:
          {==}
    case Clock.Wed{}:
      match off:
        case Clock.Mon{}:
          {==}
        case Clock.Tue{}:
          {==}
        case Clock.Wed{}:
          {==}
        case Clock.Thu{}:
          {==}
        case Clock.Fri{}:
          {==}
        case Clock.Sat{}:
          {==}
        case Clock.Sun{}:
          {==}
    case Clock.Thu{}:
      match off:
        case Clock.Mon{}:
          {==}
        case Clock.Tue{}:
          {==}
        case Clock.Wed{}:
          {==}
        case Clock.Thu{}:
          {==}
        case Clock.Fri{}:
          {==}
        case Clock.Sat{}:
          {==}
        case Clock.Sun{}:
          {==}
    case Clock.Fri{}:
      match off:
        case Clock.Mon{}:
          {==}
        case Clock.Tue{}:
          {==}
        case Clock.Wed{}:
          {==}
        case Clock.Thu{}:
          {==}
        case Clock.Fri{}:
          {==}
        case Clock.Sat{}:
          {==}
        case Clock.Sun{}:
          {==}
    case Clock.Sat{}:
      match off:
        case Clock.Mon{}:
          {==}
        case Clock.Tue{}:
          {==}
        case Clock.Wed{}:
          {==}
        case Clock.Thu{}:
          {==}
        case Clock.Fri{}:
          {==}
        case Clock.Sat{}:
          {==}
        case Clock.Sun{}:
          {==}
    case Clock.Sun{}:
      match off:
        case Clock.Mon{}:
          {==}
        case Clock.Tue{}:
          {==}
        case Clock.Wed{}:
          {==}
        case Clock.Thu{}:
          {==}
        case Clock.Fri{}:
          {==}
        case Clock.Sat{}:
          {==}
        case Clock.Sun{}:
          {==}

# twice an offset a day on is twice the offset, two days on
law plus_twice:
  for +day: Clock.Wd
  {Clock.time.wd.plus(Clock.Wed{}, Clock.time.wd.plus(day, day))
    == Clock.time.wd.plus(Clock.time.wd.plus(Clock.Tue{}, day), Clock.time.wd.plus(Clock.Tue{}, day)) : Clock.Wd}

def plus_twice(day):
  match day:
    case Clock.Mon{}:
      {==}
    case Clock.Tue{}:
      {==}
    case Clock.Wed{}:
      {==}
    case Clock.Thu{}:
      {==}
    case Clock.Fri{}:
      {==}
    case Clock.Sat{}:
      {==}
    case Clock.Sun{}:
      {==}

# n days after a day is that day plus n days after a Monday
law wd_shift:
  for +num: Nat
  for +day: Clock.Wd
  {Clock.time.wd.go(num, day) == Clock.time.wd.plus(day, Clock.time.wd.go(num, Clock.Mon{})) : Clock.Wd}

def wd_shift(num, day):
  match num:
    case 0n:
      Equal.sym(Clock.Wd, Clock.time.wd.plus(day, Clock.Mon{}), day, plus_mon(day))
    case 1n+more:
      Equal.trans(Clock.Wd, Clock.time.wd.go(more, Clock.time.wd.next(day)),
        Clock.time.wd.plus(Clock.time.wd.next(day), Clock.time.wd.go(more, Clock.Mon{})),
        Clock.time.wd.plus(day, Clock.time.wd.go(more, Clock.Tue{})),
        wd_shift(more, Clock.time.wd.next(day)),
        Equal.trans(Clock.Wd, Clock.time.wd.plus(Clock.time.wd.next(day), Clock.time.wd.go(more, Clock.Mon{})),
          Clock.time.wd.plus(day, Clock.time.wd.plus(Clock.Tue{}, Clock.time.wd.go(more, Clock.Mon{}))),
          Clock.time.wd.plus(day, Clock.time.wd.go(more, Clock.Tue{})),
          plus_step(day, Clock.time.wd.go(more, Clock.Mon{})),
          Equal.cong(Clock.Wd, Clock.Wd, y => Clock.time.wd.plus(day, y),
            Clock.time.wd.plus(Clock.Tue{}, Clock.time.wd.go(more, Clock.Mon{})),
            Clock.time.wd.go(more, Clock.Tue{}),
            Equal.sym(Clock.Wd, Clock.time.wd.go(more, Clock.Tue{}),
              Clock.time.wd.plus(Clock.Tue{}, Clock.time.wd.go(more, Clock.Mon{})),
              wd_shift(more, Clock.Tue{})))))

# twice n days after a Monday is n days after it, added to itself
law wd_double:
  for +num: Nat
  {Clock.time.wd.go(Nat.double(num), Clock.Mon{})
    == Clock.time.wd.plus(Clock.time.wd.go(num, Clock.Mon{}), Clock.time.wd.go(num, Clock.Mon{})) : Clock.Wd}

def wd_double(num):
  match num:
    case 0n:
      {==}
    case 1n+more:
      Equal.trans(Clock.Wd, Clock.time.wd.go(Nat.double(more), Clock.Wed{}),
        Clock.time.wd.plus(Clock.Wed{}, Clock.time.wd.go(Nat.double(more), Clock.Mon{})),
        Clock.time.wd.plus(Clock.time.wd.go(more, Clock.Tue{}), Clock.time.wd.go(more, Clock.Tue{})),
        wd_shift(Nat.double(more), Clock.Wed{}),
        Equal.trans(Clock.Wd,
          Clock.time.wd.plus(Clock.Wed{}, Clock.time.wd.go(Nat.double(more), Clock.Mon{})),
          Clock.time.wd.plus(Clock.Wed{}, Clock.time.wd.plus(Clock.time.wd.go(more, Clock.Mon{}),
            Clock.time.wd.go(more, Clock.Mon{}))),
          Clock.time.wd.plus(Clock.time.wd.go(more, Clock.Tue{}), Clock.time.wd.go(more, Clock.Tue{})),
          Equal.cong(Clock.Wd, Clock.Wd, y => Clock.time.wd.plus(Clock.Wed{}, y),
            Clock.time.wd.go(Nat.double(more), Clock.Mon{}),
            Clock.time.wd.plus(Clock.time.wd.go(more, Clock.Mon{}), Clock.time.wd.go(more, Clock.Mon{})),
            wd_double(more)),
          Equal.trans(Clock.Wd,
            Clock.time.wd.plus(Clock.Wed{}, Clock.time.wd.plus(Clock.time.wd.go(more, Clock.Mon{}),
              Clock.time.wd.go(more, Clock.Mon{}))),
            Clock.time.wd.plus(Clock.time.wd.plus(Clock.Tue{}, Clock.time.wd.go(more, Clock.Mon{})),
              Clock.time.wd.plus(Clock.Tue{}, Clock.time.wd.go(more, Clock.Mon{}))),
            Clock.time.wd.plus(Clock.time.wd.go(more, Clock.Tue{}), Clock.time.wd.go(more, Clock.Tue{})),
            plus_twice(Clock.time.wd.go(more, Clock.Mon{})),
            Equal.cong(Clock.Wd, Clock.Wd, +y => Clock.time.wd.plus(y, y),
              Clock.time.wd.plus(Clock.Tue{}, Clock.time.wd.go(more, Clock.Mon{})),
              Clock.time.wd.go(more, Clock.Tue{}),
              Equal.sym(Clock.Wd, Clock.time.wd.go(more, Clock.Tue{}),
                Clock.time.wd.plus(Clock.Tue{}, Clock.time.wd.go(more, Clock.Mon{})),
                wd_shift(more, Clock.Tue{}))))))

# the bit-at-a-time day of the week is the value's days after a Monday
law wd_bits:
  for +len: Nat
  for +word: Word(len)
  {Clock.time.wd.bits(len, word) == Clock.time.wd.go(Word.to_nat(len, word), Clock.Mon{}) : Clock.Wd}

def wd_bits(len, word):
  match len:
    case 0n:
      match word:
        case WNil{}:
          {==}
    case 1n+more:
      match word:
        case WCon{False{}, rest}:
          Equal.trans(Clock.Wd,
            Clock.time.wd.plus(Clock.time.wd.bits(more, rest), Clock.time.wd.bits(more, rest)),
            Clock.time.wd.plus(Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{}),
              Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{})),
            Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{}),
            Equal.cong(Clock.Wd, Clock.Wd, +y => Clock.time.wd.plus(y, y), Clock.time.wd.bits(more, rest),
              Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{}),
              wd_bits(more, rest)),
            Equal.sym(Clock.Wd, Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{}),
              Clock.time.wd.plus(Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{}),
                Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{})),
              wd_double(Word.to_nat(more, rest))))
        case WCon{True{}, rest}:
          Equal.trans(Clock.Wd,
            Clock.time.wd.next(Clock.time.wd.plus(Clock.time.wd.bits(more, rest), Clock.time.wd.bits(more, rest))),
            Clock.time.wd.next(Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{})),
            Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Tue{}),
            Equal.cong(Clock.Wd, Clock.Wd, y => Clock.time.wd.next(y),
              Clock.time.wd.plus(Clock.time.wd.bits(more, rest), Clock.time.wd.bits(more, rest)),
              Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{}),
              Equal.trans(Clock.Wd,
                Clock.time.wd.plus(Clock.time.wd.bits(more, rest), Clock.time.wd.bits(more, rest)),
                Clock.time.wd.plus(Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{}),
                  Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{})),
                Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{}),
                Equal.cong(Clock.Wd, Clock.Wd, +y => Clock.time.wd.plus(y, y), Clock.time.wd.bits(more, rest),
                  Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{}),
                  wd_bits(more, rest)),
                Equal.sym(Clock.Wd,
                  Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{}),
                  Clock.time.wd.plus(Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{}),
                    Clock.time.wd.go(Word.to_nat(more, rest), Clock.Mon{})),
                  wd_double(Word.to_nat(more, rest))))),
            Equal.trans(Clock.Wd,
              Clock.time.wd.next(Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{})),
              Clock.time.wd.plus(Clock.Tue{},
                Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{})),
              Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Tue{}),
              Equal.sym(Clock.Wd,
                Clock.time.wd.plus(Clock.Tue{},
                  Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{})),
                Clock.time.wd.next(Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{})),
                plus_tue(Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{}))),
              Equal.sym(Clock.Wd,
                Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Tue{}),
                Clock.time.wd.plus(Clock.Tue{},
                  Clock.time.wd.go(Nat.double(Word.to_nat(more, rest)), Clock.Mon{})),
                wd_shift(Nat.double(Word.to_nat(more, rest)), Clock.Tue{}))))

def Laws.weekday_days(days):
  match days:
    case U32{+word}:
      Equal.trans(U32,
        Clock.time.wd.num(Clock.time.wd.plus(Clock.Thu{}, Clock.time.wd.bits(32n, word))),
        Clock.time.wd.num(Clock.time.wd.plus(Clock.Thu{},
          Clock.time.wd.go(Word.to_nat(32n, word), Clock.Mon{}))),
        Clock.time.wd.num(Clock.time.wd.go(Word.to_nat(32n, word), Clock.Thu{})),
        Equal.cong(Clock.Wd, U32, y => Clock.time.wd.num(Clock.time.wd.plus(Clock.Thu{}, y)),
          Clock.time.wd.bits(32n, word), Clock.time.wd.go(Word.to_nat(32n, word), Clock.Mon{}),
          wd_bits(32n, word)),
        Equal.cong(Clock.Wd, U32, y => Clock.time.wd.num(y),
          Clock.time.wd.plus(Clock.Thu{}, Clock.time.wd.go(Word.to_nat(32n, word), Clock.Mon{})),
          Clock.time.wd.go(Word.to_nat(32n, word), Clock.Thu{}),
          Equal.sym(Clock.Wd, Clock.time.wd.go(Word.to_nat(32n, word), Clock.Thu{}),
            Clock.time.wd.plus(Clock.Thu{}, Clock.time.wd.go(Word.to_nat(32n, word), Clock.Mon{})),
            wd_shift(Word.to_nat(32n, word), Clock.Thu{}))))

def Laws.fields_weekday(_secs):
  {==}

def Laws.civil_iso(_secs, _ms):
  {==}

def Laws.week_rule(_secs):
  {==}

def Laws.thursday_def(_days):
  {==}

def Laws.week_of_def(_thu, _year, _month, _day):
  {==}

def Laws.week_text(_year, _num):
  {==}

def Laws.week_text_of(_secs):
  {==}

def Laws.week_text_2009(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 14242, e)
    : {Clock.time.week.text(Clock.time.week(_)) == "2009-W01" : String}
  {==}

def Laws.week_dec29_2008(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 14242, e)
    : {Clock.time.week(_) == (2009, 1) : U32 & U32}
  {==}

def Laws.week_dec31_2014(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 16435, e)
    : {Clock.time.week(_) == (2015, 1) : U32 & U32}
  {==}

def Laws.week_dec30_2019(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 18260, e)
    : {Clock.time.week(_) == (2020, 1) : U32 & U32}
  {==}

def Laws.week_dec31_2024(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 20088, e)
    : {Clock.time.week(_) == (2025, 1) : U32 & U32}
  {==}

def Laws.week_jan3_2010(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 14612, e)
    : {Clock.time.week(_) == (2009, 53) : U32 & U32}
  {==}

def Laws.week_jan1_2016(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 16801, e)
    : {Clock.time.week(_) == (2015, 53) : U32 & U32}
  {==}

def Laws.week_jan3_2021(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 18630, e)
    : {Clock.time.week(_) == (2020, 53) : U32 & U32}
  {==}

def Laws.week_jan1_2022(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 18993, e)
    : {Clock.time.week(_) == (2021, 52) : U32 & U32}
  {==}

def Laws.week_jan1_2023(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19358, e)
    : {Clock.time.week(_) == (2022, 52) : U32 & U32}
  {==}

def Laws.week_jan1_2027(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 20819, e)
    : {Clock.time.week(_) == (2026, 53) : U32 & U32}
  {==}

def Laws.week_53_2020(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 18627, e)
    : {Clock.time.week(_) == (2020, 53) : U32 & U32}
  {==}

def Laws.week_53_2026(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 20818, e)
    : {Clock.time.week(_) == (2026, 53) : U32 & U32}
  {==}

def Laws.week_52_2021(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 18992, e)
    : {Clock.time.week(_) == (2021, 52) : U32 & U32}
  {==}

def Laws.week_52_2025(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 20450, e)
    : {Clock.time.week(_) == (2025, 52) : U32 & U32}
  {==}

def Laws.week_after_52_2025(secs, e):
  %Equal.sym(U32, (secs / 86400 : U32), 20451, e)
    : {Clock.time.week(_) == (2026, 1) : U32 & U32}
  {==}

# --- text templates ---

def Laws.fill_open_empty(_close, _t, _pairs):
  {==}

def Laws.fill_close_empty(open, _t, _pairs):
  match open:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

def Laws.value_none(_key):
  {==}

def Laws.own_order(_k, _v, _rest):
  {==}

def Laws.fill_braces(_t, _pairs):
  {==}

# --- anchor days: the day number rewritten to its literal ---

def Laws.leap_2000(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 11016, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2000-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.leap_2000_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 11017, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2000-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.leap_2024(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19782, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2024-02-29T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.leap_2024_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19783, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2024-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.common_2023(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19416, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2023-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.common_2023_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 19417, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2023-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.century_2100(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 47540, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2100-02-28T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.century_2100_after(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 47541, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2100-03-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.epoch(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 0, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "1970-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.eve_2000(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 10956, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "1999-12-31T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.day_2000(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 10957, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2000-01-01T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.last_day(secs, ms, e):
  %Equal.sym(U32, (secs / 86400 : U32), 49710, e) : {Clock.time.date(_)
    ++ SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}
    == "2106-02-07T" ++ Clock.time.clock((secs % 86400 : U32), ms) : String}
  {==}

def Laws.value_hit(k, v, rest, key, e):
  %Equal.sym(Bool, String.eq(k, key), True{}, e)
    : {Text.text.value.pick(_, v, _u => Text.text.value(rest, key)) == Some{v}
      : Maybe<&2, String>}
  {==}

def Laws.value_miss(k, v, rest, key, e):
  %Equal.sym(Bool, String.eq(k, key), False{}, e)
    : {Text.text.value.pick(_, v, _u => Text.text.value(rest, key))
      == Text.text.value(rest, key) : Maybe<&2, String>}
  {==}

# --- the scan ---

def Laws.fill_plain(oh, ot, ch, ct, h, t, pairs, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, SCon{oh, ot}), False{}, e)
    : {Text.text.join(Text.text.plain(_, h, SCon{oh, ot}),
      next => Text.text.go(t, next, SCon{oh, ot}, SCon{ch, ct}, pairs))
      == SCon{h, Text.text.fill_with(SCon{oh, ot}, SCon{ch, ct}, t, pairs)}
      : String}
  {==}

# plain text with no open delimiter in it scans to itself
law go_plain:
  for +t: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(open, t) == False{} : Bool}
  {Text.text.go(t, Text.Plain{}, open, close, pairs) == t : String}

def go_plain(t, open, close, pairs, e):
  match t:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      %Equal.sym(Bool, String.starts_with(SCon{h, r}, open), False{},
        any_false_l(String.starts_with(SCon{h, r}, open),
          _u => Text.text.marked(open, r), e))
        : {Text.text.join(Text.text.plain(_, h, open),
          next => Text.text.go(r, next, open, close, pairs)) == SCon{h, r}
          : String}
      Equal.cong(String, String, x => SCon{h, x},
        Text.text.go(r, Text.Plain{}, open, close, pairs), r,
        go_plain(r, open, close, pairs,
          any_false_r(String.starts_with(SCon{h, r}, open),
            _u => Text.text.marked(open, r), e)))

def Laws.fill_unmarked(open, close, t, pairs, e):
  match open:
    case SNil{}:
      {==}
    case SCon{oh, ot}:
      match close:
        case SNil{}:
          {==}
        case SCon{ch, ct}:
          go_plain(t, SCon{oh, ot}, SCon{ch, ct}, pairs, e)

# the rest of an open delimiter is passed over into a key
law go_opening:
  for +ot: String
  for +x: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  {Text.text.go(ot ++ x, Text.text.enter(String.length(ot)), open, close, pairs)
    == Text.text.go(x, Text.InKey{""}, open, close, pairs) : String}

def go_opening(ot, x, open, close, pairs):
  match ot:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      go_opening(t, x, open, close, pairs)

# the rest of a close delimiter is passed over into plain text
law go_closing:
  for +ct: String
  for +x: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  {Text.text.go(ct ++ x, Text.text.leave(String.length(ct)), open, close, pairs)
    == Text.text.go(x, Text.Plain{}, open, close, pairs) : String}

def go_closing(ct, x, open, close, pairs):
  match ct:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      go_closing(t, x, open, close, pairs)

# a key with no close delimiter in it scans to the close that follows it,
# which writes the marker's replacement and goes on in plain text
law go_key:
  for +key: String
  for +acc: String
  for +rest: String
  for +open: String
  for +ch: Char
  for +ct: String
  for +pairs: Text.text.Pairs()
  for +free: {Text.text.free(SCon{ch, ct}, key, SCon{ch, ct} ++ rest) == True{}
    : Bool}
  {Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{acc}, open,
    SCon{ch, ct}, pairs)
    == Text.text.put(open, SCon{ch, ct}, acc ++ key,
      Text.text.value(pairs, acc ++ key))
    ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs) : String}

def go_key(key, acc, rest, open, ch, ct, pairs, free):
  match key:
    case SNil{}:
      %Equal.sym(Bool, String.starts_with(SCon{ch, ct} ++ rest, SCon{ch, ct}),
        True{}, starts_self(SCon{ch, ct}, rest))
        : {Text.text.join(Text.text.shut(_, ch, acc, open, SCon{ch, ct}, pairs),
          next => Text.text.go(ct ++ rest, next, open, SCon{ch, ct}, pairs))
          == Text.text.put(open, SCon{ch, ct}, acc ++ "",
            Text.text.value(pairs, acc ++ ""))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs)
          : String}
      %go_closing(ct, rest, open, SCon{ch, ct}, pairs)
        : {Text.text.put(open, SCon{ch, ct}, acc, Text.text.value(pairs, acc))
          ++ Text.text.go(ct ++ rest, Text.text.leave(String.length(ct)), open,
            SCon{ch, ct}, pairs)
          == Text.text.put(open, SCon{ch, ct}, acc ++ "",
            Text.text.value(pairs, acc ++ "")) ++ _ : String}
      Equal.cong(String, String,
        +x => Text.text.put(open, SCon{ch, ct}, x, Text.text.value(pairs, x))
          ++ Text.text.go(ct ++ rest, Text.text.leave(String.length(ct)), open,
            SCon{ch, ct}, pairs),
        acc, acc ++ "", Equal.sym(String, acc ++ "", acc, app_nil(acc)))
    case SCon{+h, +k}:
      %Equal.sym(Bool,
        String.starts_with(SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct}),
        False{},
        not_true(
          String.starts_with(SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct}),
          all_true_l(Bool.not(String.starts_with(
            SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct})),
            _u => Text.text.free(SCon{ch, ct}, k, SCon{ch, ct} ++ rest), free)))
        : {Text.text.join(Text.text.shut(_, h, acc, open, SCon{ch, ct}, pairs),
          next => Text.text.go(k ++ (SCon{ch, ct} ++ rest), next, open,
            SCon{ch, ct}, pairs))
          == Text.text.put(open, SCon{ch, ct}, acc ++ SCon{h, k},
            Text.text.value(pairs, acc ++ SCon{h, k}))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs)
          : String}
      Equal.trans(String,
        Text.text.go(k ++ (SCon{ch, ct} ++ rest), Text.InKey{acc ++ SCon{h, SNil{}}}, open,
          SCon{ch, ct}, pairs),
        Text.text.put(open, SCon{ch, ct}, (acc ++ SCon{h, SNil{}}) ++ k,
          Text.text.value(pairs, (acc ++ SCon{h, SNil{}}) ++ k))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs),
        Text.text.put(open, SCon{ch, ct}, acc ++ SCon{h, k},
          Text.text.value(pairs, acc ++ SCon{h, k}))
          ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs),
        go_key(k, acc ++ SCon{h, SNil{}}, rest, open, ch, ct, pairs,
          all_true_r(Bool.not(String.starts_with(
            SCon{h, k ++ (SCon{ch, ct} ++ rest)}, SCon{ch, ct})),
            _u => Text.text.free(SCon{ch, ct}, k, SCon{ch, ct} ++ rest), free)),
        Equal.cong(String, String,
          +x => Text.text.put(open, SCon{ch, ct}, x, Text.text.value(pairs, x))
            ++ Text.text.go(rest, Text.Plain{}, open, SCon{ch, ct}, pairs),
          (acc ++ SCon{h, SNil{}}) ++ k, acc ++ SCon{h, k}, app_assoc(acc, SCon{h, SNil{}}, k)))

# a key with no close delimiter in it, at the end of the template, is
# written back with its open delimiter
law go_unclosed:
  for +key: String
  for +acc: String
  for +open: String
  for +close: String
  for +pairs: Text.text.Pairs()
  for +e: {Text.text.marked(close, key) == False{} : Bool}
  {Text.text.go(key, Text.InKey{acc}, open, close, pairs)
    == open ++ (acc ++ key) : String}

def go_unclosed(key, acc, open, close, pairs, e):
  match key:
    case SNil{}:
      Equal.cong(String, String, x => open ++ x, acc, acc ++ "",
        Equal.sym(String, acc ++ "", acc, app_nil(acc)))
    case SCon{+h, +k}:
      %Equal.sym(Bool, String.starts_with(SCon{h, k}, close), False{},
        any_false_l(String.starts_with(SCon{h, k}, close),
          _u => Text.text.marked(close, k), e))
        : {Text.text.join(Text.text.shut(_, h, acc, open, close, pairs),
          next => Text.text.go(k, next, open, close, pairs))
          == open ++ (acc ++ SCon{h, k}) : String}
      Equal.trans(String,
        Text.text.go(k, Text.InKey{acc ++ SCon{h, SNil{}}}, open, close, pairs),
        open ++ ((acc ++ SCon{h, SNil{}}) ++ k),
        open ++ (acc ++ SCon{h, k}),
        go_unclosed(k, acc ++ SCon{h, SNil{}}, open, close, pairs,
          any_false_r(String.starts_with(SCon{h, k}, close),
            _u => Text.text.marked(close, k), e)),
        Equal.cong(String, String, x => open ++ x,
          (acc ++ SCon{h, SNil{}}) ++ k, acc ++ SCon{h, k},
          app_assoc(acc, SCon{h, SNil{}}, k)))

# a marker at the start of a template: the open delimiter is found, passed
# over, and the key scanned
law go_marker:
  for +oh: Char
  for +ot: String
  for +x: String
  for +close: String
  for +pairs: Text.text.Pairs()
  {Text.text.go(SCon{oh, ot} ++ x, Text.Plain{}, SCon{oh, ot}, close, pairs)
    == Text.text.go(x, Text.InKey{""}, SCon{oh, ot}, close, pairs) : String}

def go_marker(oh, ot, x, close, pairs):
  %Equal.sym(Bool, String.starts_with(SCon{oh, ot} ++ x, SCon{oh, ot}), True{},
    starts_self(SCon{oh, ot}, x))
    : {Text.text.join(Text.text.plain(_, oh, SCon{oh, ot}),
      next => Text.text.go(ot ++ x, next, SCon{oh, ot}, close, pairs))
      == Text.text.go(x, Text.InKey{""}, SCon{oh, ot}, close, pairs) : String}
  go_opening(ot, x, SCon{oh, ot}, close, pairs)

def Laws.fill_known(oh, ot, ch, ct, key, value, rest, pairs, found, free):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), Text.Plain{},
      SCon{oh, ot}, SCon{ch, ct}, pairs),
    Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
      SCon{ch, ct}, pairs),
    value ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
      pairs),
    go_marker(oh, ot, key ++ (SCon{ch, ct} ++ rest), SCon{ch, ct}, pairs),
    Equal.trans(String,
      Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
        SCon{ch, ct}, pairs),
      Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key,
        Text.text.value(pairs, key))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      value ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
        pairs),
      go_key(key, "", rest, SCon{oh, ot}, ch, ct, pairs, free),
      Equal.cong(Maybe<&2, String>, String,
        m => Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key, m)
          ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
            pairs),
        Text.text.value(pairs, key), Some{value}, found)))

def Laws.fill_unknown(oh, ot, ch, ct, key, rest, pairs, missing, free):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ (key ++ (SCon{ch, ct} ++ rest)), Text.Plain{},
      SCon{oh, ot}, SCon{ch, ct}, pairs),
    Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
      SCon{ch, ct}, pairs),
    (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
      ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
    go_marker(oh, ot, key ++ (SCon{ch, ct} ++ rest), SCon{ch, ct}, pairs),
    Equal.trans(String,
      Text.text.go(key ++ (SCon{ch, ct} ++ rest), Text.InKey{""}, SCon{oh, ot},
        SCon{ch, ct}, pairs),
      Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key,
        Text.text.value(pairs, key))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      (SCon{oh, ot} ++ (key ++ SCon{ch, ct}))
        ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct}, pairs),
      go_key(key, "", rest, SCon{oh, ot}, ch, ct, pairs, free),
      Equal.cong(Maybe<&2, String>, String,
        m => Text.text.put(SCon{oh, ot}, SCon{ch, ct}, key, m)
          ++ Text.text.go(rest, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
            pairs),
        Text.text.value(pairs, key), None{}, missing)))

def Laws.fill_unclosed(oh, ot, ch, ct, key, pairs, e):
  Equal.trans(String,
    Text.text.go(SCon{oh, ot} ++ key, Text.Plain{}, SCon{oh, ot}, SCon{ch, ct},
      pairs),
    Text.text.go(key, Text.InKey{""}, SCon{oh, ot}, SCon{ch, ct}, pairs),
    SCon{oh, ot} ++ key,
    go_marker(oh, ot, key, SCon{ch, ct}, pairs),
    go_unclosed(key, "", SCon{oh, ot}, SCon{ch, ct}, pairs, e))

# --- the form of time.iso ---

# every digit character is shaped '#'
law digit_at_shape:
  for k: Nat
  {Laws.shape.char(Clock.time.digit.at(k)) == '#' : Char}

def digit_at_shape(k):
  match k:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+_k9:
                                      {==}

# every digit time.iso writes is shaped '#'
law digit_shape:
  for n: U32
  {Laws.shape.char(Clock.time.digit(n)) == '#' : Char}

def digit_shape(n):
  digit_at_shape(U32.to_nat((n % 10 : U32)))

# shaping a joined text is joining the shaped parts
law shape_app:
  for +a: String
  for +b: String
  {Laws.shape(a ++ b) == Laws.shape(a) ++ Laws.shape(b) : String}

def shape_app(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{Laws.shape.char(h), x},
        Laws.shape(t ++ b), Laws.shape(t) ++ Laws.shape(b), shape_app(t, b))

# the shape of a date
law ymd_shape:
  for +y: U32
  for +m: U32
  for +d: U32
  {Laws.shape(Clock.time.ymd(y, m, d)) == "####-##-##" : String}

def ymd_shape(y, m, d):
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((y / 1000 : U32))), '#',
    digit_shape((y / 1000 : U32)))
    : {SCon{_, SCon{Laws.shape.char(Clock.time.digit((y / 100 : U32))),
      SCon{Laws.shape.char(Clock.time.digit((y / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(y)), SCon{'-',
          SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
              SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
                SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((y / 100 : U32))), '#',
    digit_shape((y / 100 : U32)))
    : {SCon{'#', SCon{_, SCon{Laws.shape.char(Clock.time.digit((y / 10 : U32))),
      SCon{Laws.shape.char(Clock.time.digit(y)), SCon{'-',
        SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
            SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
              SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((y / 10 : U32))), '#',
    digit_shape((y / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{_, SCon{Laws.shape.char(Clock.time.digit(y)), SCon{'-',
      SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
          SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(y)), '#', digit_shape(y))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{_, SCon{'-',
      SCon{Laws.shape.char(Clock.time.digit((m / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
          SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((m / 10 : U32))), '#',
    digit_shape((m / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit(m)), SCon{'-',
        SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(m)), '#', digit_shape(m))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{'#', SCon{_, SCon{'-',
      SCon{Laws.shape.char(Clock.time.digit((d / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((d / 10 : U32))), '#',
    digit_shape((d / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{'#', SCon{'#', SCon{'-', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit(d)), SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(d)), '#', digit_shape(d))
    : {SCon{'#', SCon{'#', SCon{'#', SCon{'#', SCon{'-', SCon{'#', SCon{'#', SCon{'-', SCon{'#',
      SCon{_, SNil{}}}}}}}}}}}
      == "####-##-##" : String}
  {==}

# the shape of the date of any year, month and day
law ymd_of_shape:
  for date: Clock.Ymd
  {Laws.shape(Clock.time.ymd.of(date)) == "####-##-##" : String}

def ymd_of_shape(date):
  match date:
    case Clock.Ymd{+y, +m, +d}:
      ymd_shape(y, m, d)

# the shape of a time of day
law clock_shape:
  for +sod: U32
  for +ms: U32
  {Laws.shape(Clock.time.clock(sod, ms)) == "##:##:##.###Z" : String}

def clock_shape(sod, ms):
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(((sod / 3600 : U32) / 10 : U32))), '#',
    digit_shape(((sod / 3600 : U32) / 10 : U32)))
    : {SCon{_, SCon{Laws.shape.char(Clock.time.digit((sod / 3600 : U32))), SCon{':',
      SCon{Laws.shape.char(Clock.time.digit(((sod % 3600 / 60 : U32) / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), SCon{':',
          SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
              SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
                SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
                  SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((sod / 3600 : U32))), '#',
    digit_shape((sod / 3600 : U32)))
    : {SCon{'#', SCon{_, SCon{':',
      SCon{Laws.shape.char(Clock.time.digit(((sod % 3600 / 60 : U32) / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), SCon{':',
          SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
              SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
                SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
                  SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(((sod % 3600 / 60 : U32) / 10 : U32))), '#',
    digit_shape(((sod % 3600 / 60 : U32) / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), SCon{':',
        SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
            SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
              SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
                SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((sod % 3600 / 60 : U32))), '#',
    digit_shape((sod % 3600 / 60 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{_, SCon{':',
      SCon{Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
          SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
            SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
              SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(((sod % 60 : U32) / 10 : U32))), '#',
    digit_shape(((sod % 60 : U32) / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{_,
      SCon{Laws.shape.char(Clock.time.digit((sod % 60 : U32))), SCon{'.',
        SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
          SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
            SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((sod % 60 : U32))), '#',
    digit_shape((sod % 60 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{_, SCon{'.',
      SCon{Laws.shape.char(Clock.time.digit((ms / 100 : U32))),
        SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
          SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((ms / 100 : U32))), '#',
    digit_shape((ms / 100 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{'.',
      SCon{_, SCon{Laws.shape.char(Clock.time.digit((ms / 10 : U32))),
        SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit((ms / 10 : U32))), '#',
    digit_shape((ms / 10 : U32)))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{'.',
      SCon{'#', SCon{_, SCon{Laws.shape.char(Clock.time.digit(ms)), SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  %Equal.sym(Char, Laws.shape.char(Clock.time.digit(ms)), '#', digit_shape(ms))
    : {SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{':', SCon{'#', SCon{'#', SCon{'.',
      SCon{'#', SCon{'#', SCon{_, SCon{'Z', SNil{}}}}}}}}}}}}}}
      == "##:##:##.###Z" : String}
  {==}

def Laws.iso_shape(secs, ms):
  Equal.trans(String,
    Laws.shape(Clock.time.iso(secs, ms)),
    Laws.shape(Clock.time.date((secs / 86400 : U32)))
      ++ SCon{'T', Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
    "####-##-##T##:##:##.###Z",
    shape_app(Clock.time.date((secs / 86400 : U32)),
      SCon{'T', Clock.time.clock((secs % 86400 : U32), ms)}),
    Equal.trans(String,
      Laws.shape(Clock.time.date((secs / 86400 : U32)))
        ++ SCon{'T', Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
      "####-##-##"
        ++ SCon{'T', Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
      "####-##-##T##:##:##.###Z",
      Equal.cong(String, String,
        x => x ++ SCon{'T',
          Laws.shape(Clock.time.clock((secs % 86400 : U32), ms))},
        Laws.shape(Clock.time.date((secs / 86400 : U32))), "####-##-##",
        ymd_of_shape(Clock.time.civil((secs / 86400 : U32)))),
      Equal.cong(String, String, x => "####-##-##" ++ SCon{'T', x},
        Laws.shape(Clock.time.clock((secs % 86400 : U32), ms)),
        "##:##:##.###Z", clock_shape((secs % 86400 : U32), ms))))

# --- errors ---

def Laws.err_table(_code, _why):
  {==}

def Laws.look_none(_code, _why):
  {==}

def Laws.look_hit(k, text, rest, code, why, e):
  %Equal.sym(Bool, U32.is_eq(code, k), True{}, e)
    : {Err.err.when(_, _u => text, _u => Err.err.look(rest, code, why))
      == text : String}
  {==}

def Laws.look_miss(k, text, rest, code, why, e):
  %Equal.sym(Bool, U32.is_eq(code, k), False{}, e)
    : {Err.err.when(_, _u => text, _u => Err.err.look(rest, code, why))
      == Err.err.look(rest, code, why) : String}
  {==}

def Laws.err_os(_code, _why, _path):
  {==}

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

# --- directories ---

def Laws.dir_fail(_code, _why):
  {==}

def Laws.dir_done(_raw):
  {==}

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
      gone(&1, {False{} == True{} : Bool}, clash(e))
    case EQ{}:
      gone(&1, {True{} == True{} : Bool}, clash(e))
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
      gone(&1, {False{} == True{} : Bool}, clash(Equal.sym(Bool, False{}, True{}, e)))
    case True{} False{}:
      gone(&1, {True{} == False{} : Bool}, clash(Equal.sym(Bool, False{}, True{}, e)))
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
      gone(&1, {False{} == True{} : Bool}, clash(Equal.sym(Bool, False{}, True{}, e)))
    case EQ{}:
      {==}
    case GT{}:
      gone(&1, {False{} == True{} : Bool}, clash(Equal.sym(Bool, False{}, True{}, e)))

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
      gone(&1, {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))
    case EQ{}:
      e
    case GT{}:
      gone(&1, {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))

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
          gone(&1, {SNil{} == SCon{Chr{y}, t2} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))
        case EQ{}:
          gone(&1, {SNil{} == SCon{Chr{y}, t2} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))
        case GT{}:
          gone(&1, {SNil{} == SCon{Chr{y}, t2} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))
    case SCon{Chr{+x}, +t1} SNil{}:
      match c:
        case LT{}:
          gone(&1, {SCon{Chr{x}, t1} == SNil{} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))
        case EQ{}:
          gone(&1, {SCon{Chr{x}, t1} == SNil{} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))
        case GT{}:
          gone(&1, {SCon{Chr{x}, t1} == SNil{} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          gone(&1, {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))
        case EQ{}:
          %u32_cmp_eq(x, y, order_eq_c(t1, t2, U32.cmp(x, y), e))
            : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
          Equal.cong(String, String, s => SCon{Chr{x}, s}, t1, t2,
            order_eq(t1, t2, U32.cmp(x, y), e))
        case GT{}:
          gone(&1, {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, clash(Equal.sym(Bool, False{}, True{}, e)))

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
      gone(&1, {False{} == True{} : Bool},
        clash(Equal.sym(Bool, False{}, True{}, e)))
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
      gone(&1, {b == True{} : Bool}, clash(Equal.sym(Bool, False{}, True{}, e)))
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

# --- whitespace ---

# a false is not true
def no(-G: Type, e: {False{} == True{} : Bool}) -> G:
  gone(&1, G, clash(Equal.sym(Bool, False{}, True{}, e)))

def Laws.space_set(_x):
  {==}

def Laws.lstrip_space(h, t, e):
  %Equal.sym(Bool, Str.text.space(h), True{}, e)
    : {Str.text.lstrip.if(_, h, t, _u => Str.text.lstrip(t))
      == Str.text.lstrip(t) : String}
  {==}

def Laws.lstrip_keep(h, t, e):
  %Equal.sym(Bool, Str.text.space(h), False{}, e)
    : {Str.text.lstrip.if(_, h, t, _u => Str.text.lstrip(t)) == SCon{h, t}
      : String}
  {==}

def Laws.lstrip_empty(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      no({Str.text.lstrip(SCon{h, t}) == SCon{h, t} : String}, e)

def Laws.rstrip_space(t, h, e):
  match t:
    case SNil{}:
      %Equal.sym(Bool, Str.text.space(h), True{}, e)
        : {Str.text.rstrip.lone(_, h) == SNil{} : String}
      {==}
    case SCon{+x, +r}:
      Equal.cong(String, String, y => Str.text.rstrip.put(x, y),
        Str.text.rstrip(r ++ SCon{h, SNil{}}), Str.text.rstrip(r),
        Laws.rstrip_space(r, h, e))

# a character before a nonempty rest is kept
law rstrip_put_con:
  for +x: Char
  for +r: String
  for +h: Char
  {Str.text.rstrip.put(x, r ++ SCon{h, SNil{}}) == SCon{x, r ++ SCon{h, SNil{}}}
    : String}

def rstrip_put_con(_x, r, _h):
  match r:
    case SNil{}:
      {==}
    case SCon{_a, _b}:
      {==}

def Laws.rstrip_keep(t, h, e):
  match t:
    case SNil{}:
      %Equal.sym(Bool, Str.text.space(h), False{}, e)
        : {Str.text.rstrip.lone(_, h) == SCon{h, SNil{}} : String}
      {==}
    case SCon{+x, +r}:
      Equal.trans(String,
        Str.text.rstrip.put(x, Str.text.rstrip(r ++ SCon{h, SNil{}})),
        Str.text.rstrip.put(x, r ++ SCon{h, SNil{}}),
        SCon{x, r ++ SCon{h, SNil{}}},
        Equal.cong(String, String, y => Str.text.rstrip.put(x, y),
          Str.text.rstrip(r ++ SCon{h, SNil{}}), r ++ SCon{h, SNil{}},
          Laws.rstrip_keep(r, h, e)),
        rstrip_put_con(x, r, h))

def Laws.rstrip_empty(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      no({Str.text.rstrip(SCon{h, t}) == SCon{h, t} : String}, e)

def Laws.strip_both(_s):
  {==}

# --- replace, split and find ---

# the rest of a found `old` is passed over
law replace_skip:
  for +ot: String
  for +x: String
  for +old: String
  for +new: String
  {Str.text.replace.go(ot ++ x, String.length(ot), old, new)
    == Str.text.replace.go(x, 0n, old, new) : String}

def replace_skip(ot, x, old, new):
  match ot:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      replace_skip(t, x, old, new)

def Laws.replace_hit(oh, ot, rest, new):
  %Equal.sym(Bool, String.starts_with(SCon{oh, ot} ++ rest, SCon{oh, ot}),
    True{}, starts_self(SCon{oh, ot}, rest))
    : {Str.text.replace.at(_, oh, new, String.length(ot),
      k => Str.text.replace.go(ot ++ rest, k, SCon{oh, ot}, new))
      == new ++ Str.text.replace.go(rest, 0n, SCon{oh, ot}, new) : String}
  Equal.cong(String, String, y => new ++ y,
    Str.text.replace.go(ot ++ rest, String.length(ot), SCon{oh, ot}, new),
    Str.text.replace.go(rest, 0n, SCon{oh, ot}, new),
    replace_skip(ot, rest, SCon{oh, ot}, new))

def Laws.replace_miss(h, t, oh, ot, new, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, SCon{oh, ot}), False{}, e)
    : {Str.text.replace.at(_, h, new, String.length(ot),
      k => Str.text.replace.go(t, k, SCon{oh, ot}, new))
      == SCon{h, Str.text.replace.go(t, 0n, SCon{oh, ot}, new)} : String}
  {==}

def Laws.replace_end(_oh, _ot, _new):
  {==}

def Laws.replace_gaps(_h, _t, _new):
  {==}

def Laws.replace_gaps_end(new):
  app_nil(new)

def Laws.split_end(_sh, _st):
  {==}

# the rest of a found separator is passed over
law split_skip:
  for +st: String
  for +x: String
  for +sep: String
  {Str.text.split.go(st ++ x, String.length(st), sep)
    == Str.text.split.go(x, 0n, sep) : List<&2, String>}

def split_skip(st, x, sep):
  match st:
    case SNil{}:
      {==}
    case SCon{_c, +t}:
      split_skip(t, x, sep)

def Laws.split_hit(sh, st, rest):
  %Equal.sym(Bool, String.starts_with(SCon{sh, st} ++ rest, SCon{sh, st}),
    True{}, starts_self(SCon{sh, st}, rest))
    : {Str.text.split.at(_, sh, String.length(st),
      k => Str.text.split.go(st ++ rest, k, SCon{sh, st}))
      == SNil{} <> Str.text.split.go(rest, 0n, SCon{sh, st})
      : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, y => SNil{} <> y,
    Str.text.split.go(st ++ rest, String.length(st), SCon{sh, st}),
    Str.text.split.go(rest, 0n, SCon{sh, st}),
    split_skip(st, rest, SCon{sh, st}))

def Laws.split_miss(h, t, sh, st, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, SCon{sh, st}), False{}, e)
    : {Str.text.split.at(_, h, String.length(st),
      k => Str.text.split.go(t, k, SCon{sh, st}))
      == Str.text.split.push(h, Str.text.split.go(t, 0n, SCon{sh, st}))
      : List<&2, String>}
  {==}

def Laws.split_push(_h, _p, _ps):
  {==}

# pushing a character never answers no pieces
law push_some:
  for h: Char
  for ps: List<&2, String>
  {List.is_empty(&2, String, Str.text.split.push(h, ps)) == False{} : Bool}

def push_some(_h, ps):
  match ps:
    case Nil{}:
      {==}
    case _p <> _r:
      {==}

# a step of the scan never answers no pieces
law split_at_some:
  for b: Bool
  for h: Char
  for left: Nat
  for next: Nat -> List<&2, String>
  {List.is_empty(&2, String, Str.text.split.at(b, h, left, next)) == False{}
    : Bool}

def split_at_some(b, h, _left, next):
  match b:
    case True{}:
      {==}
    case False{}:
      push_some(h, next(0n))

# the scan never answers no pieces
law split_go_some:
  for +s: String
  for +skip: Nat
  for +sep: String
  {List.is_empty(&2, String, Str.text.split.go(s, skip, sep)) == False{}
    : Bool}

def split_go_some(s, skip, sep):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match skip:
        case 0n:
          split_at_some(String.starts_with(SCon{h, t}, sep), h,
            Str.text.after(sep), k => Str.text.split.go(t, k, sep))
        case 1n+k:
          split_go_some(t, k, sep)

def Laws.split_some(s, sh, st):
  split_go_some(s, 0n, SCon{sh, st})

def Laws.split_whole(_s):
  {==}

def Laws.find_empty(s):
  match s:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

def Laws.find_hit(h, t, needle, e):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, needle), True{}, e)
    : {Str.text.find.at(_, _u => Str.text.find(t, needle)) == Some{0}
      : Maybe<&2, U32>}
  {==}

def Laws.find_next(h, t, needle, i, e, got):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, needle), False{}, e)
    : {Str.text.find.at(_, _u => Str.text.find(t, needle))
      == Some{(i + 1 : U32)} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, Str.text.find(t, needle), Some{i}, got)
    : {Str.text.find.inc(_) == Some{(i + 1 : U32)} : Maybe<&2, U32>}
  {==}

def Laws.find_none(h, t, needle, e, got):
  %Equal.sym(Bool, String.starts_with(SCon{h, t}, needle), False{}, e)
    : {Str.text.find.at(_, _u => Str.text.find(t, needle)) == None{}
      : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, Str.text.find(t, needle), None{}, got)
    : {Str.text.find.inc(_) == None{} : Maybe<&2, U32>}
  {==}

def Laws.find_end(_nh, _nt):
  {==}

# a place one further on is a place exactly when the first is
law inc_some:
  for m: Maybe<&2, U32>
  {Maybe.is_some(&2, U32, Str.text.find.inc(m)) == Maybe.is_some(&2, U32, m)
    : Bool}

def inc_some(m):
  match m:
    case None{}:
      {==}
    case Some{_i}:
      {==}

# one step of find answers a place exactly when one step of contains holds
law find_at_some:
  for b: Bool
  for +t: String
  for +needle: String
  for ih: {Maybe.is_some(&2, U32, Str.text.find(t, needle))
    == String.contains(t, needle) : Bool}
  {Maybe.is_some(&2, U32, Str.text.find.at(b, _u => Str.text.find(t, needle)))
    == String.contains.if(t, needle, b) : Bool}

def find_at_some(b, t, needle, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool,
        Maybe.is_some(&2, U32, Str.text.find.inc(Str.text.find(t, needle))),
        Maybe.is_some(&2, U32, Str.text.find(t, needle)),
        String.contains(t, needle),
        inc_some(Str.text.find(t, needle)), ih)

def Laws.find_contains(s, needle):
  match s:
    case SNil{}:
      match needle:
        case SNil{}:
          {==}
        case SCon{_h, _t}:
          {==}
    case SCon{+h, +t}:
      find_at_some(String.starts_with(SCon{h, t}, needle), t, needle,
        Laws.find_contains(t, needle))

# --- case ---

def Laws.lower_con(_h, _t):
  {==}

def Laws.lower_nil(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      no({Str.text.lower(SCon{h, t}) == SCon{h, t} : String}, e)

def Laws.upper_con(_h, _t):
  {==}

def Laws.upper_nil(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      no({Str.text.upper(SCon{h, t}) == SCon{h, t} : String}, e)

def Laws.lower_table(_x):
  {==}

def Laws.upper_table(_x):
  {==}

def Laws.case_multi(ms, rules, x, s, e):
  %Equal.sym(Maybe<&2, String>, Str.text.case.multi(ms, x), Some{s}, e)
    : {Str.text.case.one(_, x, rules) == s : String}
  {==}

def Laws.case_rules(ms, rules, x, e):
  %Equal.sym(Maybe<&2, String>, Str.text.case.multi(ms, x), None{}, e)
    : {Str.text.case.one(_, x, rules)
      == SCon{Chr{Str.text.case.apply(rules, x)}, SNil{}} : String}
  {==}

def Laws.multi_none(_x):
  {==}

def Laws.multi_hit(from, to, rest, x, e):
  %Equal.sym(Bool, U32.is_eq(from, x), True{}, e)
    : {Str.text.case.found(_, to, _u => Str.text.case.multi(rest, x))
      == Some{to} : Maybe<&2, String>}
  {==}

def Laws.multi_miss(from, to, rest, x, e):
  %Equal.sym(Bool, U32.is_eq(from, x), False{}, e)
    : {Str.text.case.found(_, to, _u => Str.text.case.multi(rest, x))
      == Str.text.case.multi(rest, x) : Maybe<&2, String>}
  {==}

def Laws.apply_none(_x):
  {==}

def Laws.apply_hit(r, rest, x, e):
  %Equal.sym(Bool, Str.text.case.covers(r, x), True{}, e)
    : {Str.text.case.pick(_, r, x, _u => Str.text.case.apply(rest, x))
      == Str.text.case.target(r, x) : U32}
  {==}

def Laws.apply_miss(r, rest, x, e):
  %Equal.sym(Bool, Str.text.case.covers(r, x), False{}, e)
    : {Str.text.case.pick(_, r, x, _u => Str.text.case.apply(rest, x))
      == Str.text.case.apply(rest, x) : U32}
  {==}

def Laws.covers_def(_lo, _hi, _step, _to, _x):
  {==}

def Laws.target_def(_lo, _hi, _step, _to, _x):
  {==}

# --- width ---

def Laws.pad_form(s, n):
  match s:
    case SNil{}:
      match n:
        case 0n:
          {==}
        case 1n+_k:
          {==}
    case SCon{+h, +t}:
      match n:
        case 0n:
          Equal.sym(String, SCon{h, t} ++ "", SCon{h, t}, app_nil(SCon{h, t}))
        case 1n+k:
          Equal.cong(String, String, y => SCon{h, y}, Str.text.pad_right(t, k),
            t ++ String.repeat(" ", Nat.sub(k, String.length(t))),
            Laws.pad_form(t, k))

# n spaces are n code points
law repeat_len:
  for n: Nat
  {String.length(String.repeat(" ", n)) == n : Nat}

def repeat_len(n):
  match n:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(Nat, Nat, m => 1n+m, String.length(String.repeat(" ", k)), k,
        repeat_len(k))

def Laws.pad_length(s, n):
  match s:
    case SNil{}:
      repeat_len(n)
    case SCon{+h, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          Equal.cong(Nat, Nat, m => 1n+m,
            String.length(Str.text.pad_right(t, k)),
            Nat.max(String.length(t), k), Laws.pad_length(t, k))

def Laws.trunc_split(s, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          Equal.cong(String, String, y => SCon{h, y},
            Str.text.truncate(t, k) ++ String.drop(t, k), t,
            Laws.trunc_split(t, k))

def Laws.trunc_length(s, n):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          Equal.cong(Nat, Nat, m => 1n+m,
            String.length(Str.text.truncate(t, k)),
            Nat.min(String.length(t), k), Laws.trunc_length(t, k))

# --- digit strings ---

def Laws.dig_rule(_a, _b):
  {==}

def Laws.dig_shorter(_a, _b):
  {==}

def Laws.dig_longer(_a, _b):
  {==}

def Laws.dig_same(_a, _b):
  {==}

def Laws.trim_zero(_t):
  {==}

def Laws.trim_keep(h, t, e):
  %Equal.sym(Bool, Char.is_eq(h, '0'), False{}, e)
    : {Str.text.digits.zero.if(_, h, t, _u => Str.text.digits.trim(t))
      == SCon{h, t} : String}
  {==}

def Laws.trim_empty(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      no({Str.text.digits.trim(SCon{h, t}) == SCon{h, t} : String}, e)

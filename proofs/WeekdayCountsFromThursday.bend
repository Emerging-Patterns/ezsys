# proofs of laws/WeekdayCountsFromThursday.bend
import Base
import ../src/clock.bend as Clock
import ../laws/WeekdayCountsFromThursday.bend as Laws

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

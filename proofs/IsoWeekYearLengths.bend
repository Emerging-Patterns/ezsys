# proofs of laws/IsoWeekYearLengths.bend
import Base
import ../src/clock.bend as Clock
import ../laws/IsoWeekYearLengths.bend as Laws

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

# proofs of laws/InputBoundariesDated.bend
import Base
import ../src/clock.bend as Clock
import ../laws/InputBoundariesDated.bend as Laws

def Laws.last_second(_ms):
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

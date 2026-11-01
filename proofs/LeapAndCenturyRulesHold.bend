# proofs of laws/LeapAndCenturyRulesHold.bend
import Base
import ../src/clock.bend as Clock
import ../laws/LeapAndCenturyRulesHold.bend as Laws

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

# proofs of laws/IsoWeekYearBoundaries.bend
import Base
import ../src/clock.bend as Clock
import ../laws/IsoWeekYearBoundaries.bend as Laws

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

# proofs of laws/IsoHasFixedShape.bend
import Base
import ../src/clock.bend as Clock
import ../laws/IsoHasFixedShape.bend as Laws

# --- wall clock ---

def Laws.iso_width(_secs, _ms):
  {==}

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

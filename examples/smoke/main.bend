# ezsys smoke: save a file atomically, read it back, print the wall clock,
# fill a template, list a directory, write a failure as Python does
import Base
import ../../main.bend as Sys

# a read's answer, as a line
def shown(res: Result<&1, &1, U32 & String, String>) -> String:
  match res:
    case Fail{(code, why)}:
      "FAIL " ++ U32.show(code) ++ " " ++ why
    case Done{text}:
      "read back: " ++ text

# a save's answer, as a line
def saved(res: Result<&1, &1, U32 & String, Unit>) -> String:
  match res:
    case Fail{(code, why)}:
      "save FAIL " ++ U32.show(code) ++ " " ++ why
    case Done{_u}:
      "saved"

# a directory's names, one line each, or the failure as Python writes it
def listed(
  +dir: String,
  res: Result<&1, &1, U32 & String, List<&2, String>>
) -> String:
  match res:
    case Fail{(code, why)}:
      Sys.err.os(code, why, dir)
    case Done{names}:
      String.join(names, "\n")

# save, read back, read a missing file, then the clock, env and templates
def main() -> IO(Unit):
  do IO<Unit>:
    +dir : String <- Sys.env.or("SMOKE_DIR", "/tmp")
    +path : String = dir ++ "/ezsys-smoke.txt"
    s : Result<&1, &1, U32 & String, Unit> <- Sys.file.save(path, "héllo, ezsys\nline two\n")
    IO.print(saved(s))
    r : Result<&1, &1, U32 & String, String> <- Sys.file.read(path)
    IO.print(shown(r))
    m : Result<&1, &1, U32 & String, String> <- Sys.file.read(dir ++ "/no-such-file")
    IO.print(shown(m))
    +now : String <- Sys.time.now_iso()
    IO.print("now: " ++ now)
    unset : String <- Sys.env.or("EZSYS_UNSET_VAR", "fallback")
    IO.print("env: " ++ unset)
    IO.print(Sys.text.fill("Hello {{name}}, it is {{when}} {{unknown}}", [("name", "Noah"), ("when", now)]))
    IO.print(Sys.text.fill_with("<!--", "-->", "<ul>\n  <!--HOSTS-->\n</ul>", [("HOSTS", "<li>pylon</li>")]))
    IO.print("text: " ++ Sys.text.upper(Sys.text.strip("\u{A0} straße \u{3000}"))
      ++ "|" ++ String.join(Sys.text.split(Sys.text.replace("a--b--c", "--", "+"), "+"), ",")
      ++ "|" ++ Sys.text.pad_right(Sys.text.truncate("ΑΒΓΔ", 2n), 4n) ++ "|")
    l : Result<&1, &1, U32 & String, List<&2, String>> <- Sys.dir.list(dir)
    IO.print("list:\n" ++ listed(dir, l))
    n : Result<&1, &1, U32 & String, List<&2, String>> <- Sys.dir.list(dir ++ "/no-such-dir")
    IO.print(listed(dir ++ "/no-such-dir", n))

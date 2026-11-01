# For every code and `why`, the text of the code is the text of the first
# entry for it in the table `strerror`, and exactly `why` when the table has
# no entry for it.
import Base
import ../src/text.bend as Text
import ../src/errno.bend as Err

# --- errors ---

# the common Linux codes and glibc's text for each, as Python's os.strerror
# gives it
def strerror() -> Err.err.Table():
  [
    (1, "Operation not permitted"),
    (2, "No such file or directory"),
    (3, "No such process"),
    (4, "Interrupted system call"),
    (5, "Input/output error"),
    (6, "No such device or address"),
    (7, "Argument list too long"),
    (8, "Exec format error"),
    (9, "Bad file descriptor"),
    (10, "No child processes"),
    (11, "Resource temporarily unavailable"),
    (12, "Cannot allocate memory"),
    (13, "Permission denied"),
    (14, "Bad address"),
    (15, "Block device required"),
    (16, "Device or resource busy"),
    (17, "File exists"),
    (18, "Invalid cross-device link"),
    (19, "No such device"),
    (20, "Not a directory"),
    (21, "Is a directory"),
    (22, "Invalid argument"),
    (23, "Too many open files in system"),
    (24, "Too many open files"),
    (25, "Inappropriate ioctl for device"),
    (26, "Text file busy"),
    (27, "File too large"),
    (28, "No space left on device"),
    (29, "Illegal seek"),
    (30, "Read-only file system"),
    (31, "Too many links"),
    (32, "Broken pipe"),
    (33, "Numerical argument out of domain"),
    (34, "Numerical result out of range"),
    (35, "Resource deadlock avoided"),
    (36, "File name too long"),
    (37, "No locks available"),
    (38, "Function not implemented"),
    (39, "Directory not empty"),
    (40, "Too many levels of symbolic links"),
    (84, "Invalid or incomplete multibyte or wide character"),
    (95, "Operation not supported"),
    (110, "Connection timed out"),
    (111, "Connection refused"),
    (112, "Host is down"),
    (113, "No route to host"),
    (116, "Stale file handle"),
    (122, "Disk quota exceeded"),
    (125, "Operation canceled")
  ]

# LAW: a code's text is looked up in strerror, with why for a code it lacks
law err_table:
  for +code: U32
  for +why: String
  {Err.err.text(code, why) == Err.err.look(strerror(), code, why) : String}

# LAW: a code no entry has is written with why
law look_none:
  for +code: U32
  for +why: String
  {Err.err.look(Nil{}, code, why) == why : String}

# LAW: the first entry with the code gives its text
law look_hit:
  for k: U32
  for text: String
  for rest: Err.err.Table()
  for +code: U32
  for +why: String
  for e: {U32.is_eq(code, k) == True{} : Bool}
  {Err.err.look(Con{(k, text), rest}, code, why) == text : String}

# LAW: an entry with another code is passed over
law look_miss:
  for k: U32
  for text: String
  for rest: Err.err.Table()
  for +code: U32
  for +why: String
  for e: {U32.is_eq(code, k) == False{} : Bool}
  {Err.err.look(Con{(k, text), rest}, code, why)
    == Err.err.look(rest, code, why) : String}

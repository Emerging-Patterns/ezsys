// ezsys.list: the names in a directory, in the order readdir(3) answers
// them, "." and ".." among them when it answers those.
//
// The path arrives as a string. On an IO helper thread, as Base's file
// effects run, the directory is opened with opendir(3), read to its end with
// readdir(3) and closed with closedir(3) before the answer is built, so it
// is never held open after the effect. The names are copied out as they are:
// no entry is followed, so a symbolic link is listed by its own name. The
// answer is Done{names} or Fail{(errno, strerror(errno))} when the open or a
// read fails; it never ends the process. Each name's bytes are decoded as
// UTF-8 by io_str, which writes U+FFFD for an invalid sequence.
#include <dirent.h>

static void ezsys_list_call(IoWork* w) {
  char* path = w->data;
  w->data = NULL;
  w->size = 0;
  DIR* d = opendir(path);
  free(path);
  if (d == NULL) {
    w->code = (u32)errno;
    return;
  }
  size_t cap = 4096;
  size_t n = 0;
  char* buf = malloc(cap);
  if (buf == NULL) {
    closedir(d);
    w->code = ENOMEM;
    return;
  }
  for (;;) {
    errno = 0;
    struct dirent* ent = readdir(d);
    if (ent == NULL) {
      break;
    }
    size_t k = strlen(ent->d_name) + 1;
    if (n + k > cap) {
      while (n + k > cap) {
        cap *= 2;
      }
      char* more = realloc(buf, cap);
      if (more == NULL) {
        free(buf);
        closedir(d);
        w->code = ENOMEM;
        return;
      }
      buf = more;
    }
    memcpy(buf + n, ent->d_name, k);
    n += k;
  }
  int err = errno;
  closedir(d);
  if (err != 0) {
    free(buf);
    w->code = (u32)err;
    return;
  }
  w->data = buf;
  w->size = n;
}

// the names, each ended by a NUL, become a list in their order
static Term ezsys_list_pack(Env e, IoWork* w) {
  Term xs = term_pak(CID(Nil), 0);
  if (w->code == 0) {
    u64 i = w->size;
    while (i > 0) {
      u64 end = i - 1;
      u64 k = end;
      while (k > 0 && w->data[k - 1] != 0) {
        k -= 1;
      }
      xs = io_node(e, CID(Con), io_str(e, w->data + k, end - k), xs);
      i = k;
    }
  }
  free(w->data);
  w->data = NULL;
  return io_res(e, w, xs);
}

Term ezsys_list_run(Env e, Term* f, IoWork* w) {
  uint64_t pn = 0;
  char* path = io_cstr(e, f[0], &pn);
  w->code = 0;
  if (io_nul(path, pn)) {
    free(path);
    w->data = NULL;
    w->size = 0;
    w->code = EILSEQ;
    return ezsys_list_pack(e, w);
  }
  w->data = path;
  return io_work(w, ezsys_list_call, ezsys_list_pack);
}

static void __attribute__((constructor)) ezsys_list_use(void) {
  io_eff(CID(ezsys.list), ezsys_list_run);
}

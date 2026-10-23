// ezsys.rename: flush a file to disk, then rename it over another name.
//
// The two paths arrive as two strings. The file at `from` is opened, fsync'd
// and closed, then rename(2) moves it to `to`. On one filesystem rename(2)
// is atomic: a reader of `to` sees the old file or the new one, never part
// of either. The answer is Done{Unit} or Fail{(errno, strerror(errno))};
// when the flush fails nothing is renamed. The directory is not fsync'd, so
// a crash just after the rename may still lose the rename itself, though not
// the file's contents. The work runs on an IO helper thread, as Base's file
// effects do.
#include <fcntl.h>
#include <stdio.h>

static void ezsys_rename_call(IoWork* w) {
  const char* from = w->data;
  const char* to = w->data + w->word;
  int fd = open(from, O_RDONLY);
  if (fd < 0) {
    w->code = (u32)errno;
    return;
  }
  if (fsync(fd) != 0) {
    w->code = (u32)errno;
    close(fd);
    return;
  }
  close(fd);
  io_sys_end(w, rename(from, to));
}

static Term ezsys_rename_pack(Env e, IoWork* w) {
  free(w->data);
  return io_res(e, w, term_pak(CID(Unit), 0));
}

Term ezsys_rename_run(Env e, Term* f, IoWork* w) {
  uint64_t fn = 0;
  uint64_t tn = 0;
  char* from = io_cstr(e, f[0], &fn);
  char* to = io_cstr(e, f[1], &tn);
  w->code = 0;
  if (io_nul(from, fn) || io_nul(to, tn)) {
    free(from);
    free(to);
    w->data = NULL;
    w->code = EILSEQ;
    return ezsys_rename_pack(e, w);
  }
  // both names in one block, `to` starting at w->word
  w->data = io_mem(malloc(fn + tn + 2));
  memcpy(w->data, from, fn);
  w->data[fn] = 0;
  memcpy(w->data + fn + 1, to, tn);
  w->data[fn + 1 + tn] = 0;
  w->word = (u32)(fn + 1);
  free(from);
  free(to);
  return io_work(w, ezsys_rename_call, ezsys_rename_pack);
}

static void __attribute__((constructor)) ezsys_rename_use(void) {
  io_eff(CID(ezsys.rename), ezsys_rename_run);
}

// ezsys.clock: the wall clock, CLOCK_REALTIME, as whole seconds since
// 1970-01-01T00:00:00Z and the milliseconds past that second. The seconds
// are cut to 32 bits, which holds until 2106-02-07T06:28:15Z.

Term ezsys_clock_run(Env e, Term* f, IoWork* w) {
  struct timespec ts;
  if (clock_gettime(CLOCK_REALTIME, &ts) != 0) {
    ts.tv_sec = 0;
    ts.tv_nsec = 0;
  }
  return io_tup(e, (Term)(uint32_t)ts.tv_sec,
    (Term)(uint32_t)(ts.tv_nsec / 1000000));
}

static void __attribute__((constructor)) ezsys_clock_use(void) {
  io_eff(CID(ezsys.clock), ezsys_clock_run);
}

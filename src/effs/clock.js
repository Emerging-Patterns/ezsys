// ezsys.clock: the JS lane's twin of clock.c. Date.now() is milliseconds
// since 1970-01-01T00:00:00Z; the seconds are cut to 32 bits, as in C.

function ezsys_clock() {
  const now = Date.now();
  return io_tup(Math.floor(now / 1000) >>> 0, now % 1000);
}

io_eff(CID(ezsys.clock), ezsys_clock);

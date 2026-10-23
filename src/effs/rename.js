// ezsys.rename: the JS lane's twin of rename.c, and the same answer. The file
// at `from` is opened, fsync'd and closed, then renamed over `to`; on a
// failure nothing more is done and the answer is the errno.

function ezsys_rename_errno(e) {
  if (typeof e.errno === "number" && e.errno !== 0) {
    return Math.abs(e.errno);
  }
  const known = require("os").constants.errno[e.code];
  return typeof known === "number" ? known : 5;
}

function ezsys_rename(from, to) {
  const fs = require("fs");
  const a = io_bytes(from);
  const b = io_bytes(to);
  if (a.includes(0) || b.includes(0)) {
    return io_fail(process.platform === "darwin" ? 92 : 84);
  }
  const src = Buffer.from(a);
  const dst = Buffer.from(b);
  try {
    const fd = fs.openSync(src, "r");
    try {
      fs.fsyncSync(fd);
    } finally {
      fs.closeSync(fd);
    }
    fs.renameSync(src, dst);
    return io_done({$: CID(Unit)});
  } catch (e) {
    return io_fail(ezsys_rename_errno(e));
  }
}

io_eff(CID(ezsys.rename), ezsys_rename);

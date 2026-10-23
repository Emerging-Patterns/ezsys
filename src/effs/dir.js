// ezsys.list: the JS lane's twin of dir.c, and the same answer: the names in
// a directory as the host lists them (fs.readdirSync, which leaves out "."
// and ".."), each decoded as UTF-8 with U+FFFD for an invalid sequence, or
// the errno when the directory cannot be read. No entry is followed.

function ezsys_list_errno(e) {
  if (typeof e.errno === "number" && e.errno !== 0) {
    return Math.abs(e.errno);
  }
  const known = require("os").constants.errno[e.code];
  return typeof known === "number" ? known : 5;
}

function ezsys_list(path) {
  const fs = require("fs");
  const p = io_bytes(path);
  if (p.includes(0)) {
    return io_fail(process.platform === "darwin" ? 92 : 84);
  }
  let names;
  try {
    names = fs.readdirSync(Buffer.from(p), { encoding: "buffer" });
  } catch (e) {
    return io_fail(ezsys_list_errno(e));
  }
  const dec = new TextDecoder("utf-8", { ignoreBOM: true });
  let xs = { $: CID(Nil) };
  for (let i = names.length; i > 0; i -= 1) {
    xs = { $: CID(Con), head: dec.decode(names[i - 1]), tail: xs };
  }
  return io_done(xs);
}

io_eff(CID(ezsys.list), ezsys_list);

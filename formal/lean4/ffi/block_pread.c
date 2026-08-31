/* POSIX positioned-read adapter for the native IBK2 executable probe.
 * It owns no RDF/SPARQL logic: Lean supplies checked offset/length plans and
 * rejects an empty/short result.  This module is intentionally not linked by
 * the WASM build. */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

static lean_obj_res l4_empty_bytes(void) { return lean_alloc_sarray(1, 0, 0); }

LEAN_EXPORT lean_obj_res l4_block_pread(b_lean_obj_arg path, uint64_t offset,
                                        uint64_t length, lean_obj_arg world) {
  (void)world;
  if (length > SIZE_MAX || offset > INT64_MAX) return lean_io_result_mk_ok(l4_empty_bytes());
  int fd = open(lean_string_cstr(path), O_RDONLY);
  if (fd < 0) return lean_io_result_mk_ok(l4_empty_bytes());
  lean_obj_res out = lean_alloc_sarray(1, (size_t)length, (size_t)length);
  size_t done = 0;
  while (done < (size_t)length) {
    ssize_t n = pread(fd, lean_sarray_cptr(out) + done, (size_t)length - done,
                      (off_t)offset + (off_t)done);
    if (n > 0) { done += (size_t)n; continue; }
    if (n < 0 && errno == EINTR) continue;
    close(fd); lean_dec(out); return lean_io_result_mk_ok(l4_empty_bytes());
  }
  close(fd);
  return lean_io_result_mk_ok(out);
}

/* Compare-and-append is the multi-writer form used by the DLOG host. The
 * caller parsed a particular complete byte sequence and supplies its length;
 * under an exclusive advisory lock we append only if the file still has that
 * length. A concurrent winner makes this return false, so Lean reloads the
 * committed sequence, allocates a fresh sequence number, and retries. */
LEAN_EXPORT lean_obj_res l4_delta_log_append_sync_at_size(
    b_lean_obj_arg path, uint64_t expected_size, b_lean_obj_arg bytes,
    lean_obj_arg world) {
  (void)world;
  int ok = 0;
  int fd = open(lean_string_cstr(path), O_WRONLY | O_CREAT | O_APPEND, 0644);
  if (fd < 0) return lean_io_result_mk_ok(lean_box(0));
  if (flock(fd, LOCK_EX) != 0) { close(fd); return lean_io_result_mk_ok(lean_box(0)); }
  struct stat st;
  if (fstat(fd, &st) == 0 && st.st_size >= 0 &&
      (uint64_t)st.st_size == expected_size) {
    size_t total = lean_sarray_size(bytes);
    size_t done = 0;
    ok = 1;
    while (done < total) {
      ssize_t n = write(fd, lean_sarray_cptr(bytes) + done, total - done);
      if (n > 0) { done += (size_t)n; continue; }
      if (n < 0 && errno == EINTR) continue;
      ok = 0;
      break;
    }
    if (ok && fsync(fd) != 0) ok = 0;
  }
  flock(fd, LOCK_UN);
  if (close(fd) != 0) ok = 0;
  return lean_io_result_mk_ok(lean_box(ok));
}

# The compiler, as a published artifact.
#
# This image is the whole of what the compiler repo promises the outside world: one
# executable, with the CLI contract documented in packaging/README.md. It is consumed as a
# build stage by downstream images (`COPY --from=compiler`), and is runnable on its own so
# that `docker run … --help` works when you are debugging what was actually published.
#
# The binary is built on the runner and copied in, rather than built here. Building Lean
# inside the image would mean no Mathlib cache and a 40-minute layer that reruns on every
# unrelated change; this way the image build is a file copy.

FROM debian:bookworm-slim

# The binary is dynamically linked against glibc and nothing else — no Lean toolchain, no
# shared objects to ship alongside it.
COPY stlc /usr/local/bin/stlc

ENTRYPOINT ["/usr/local/bin/stlc"]

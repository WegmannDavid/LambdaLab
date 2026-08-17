# The published artifact

What this repo promises to anything downstream. Everything here is checked by CI; nothing
here is a verbal agreement.

```
ARTIFACT  ghcr.io/wegmanndavid/lambdalab-compiler:{latest,<sha>}
  /usr/local/bin/stlc      executable, dynamically linked against glibc only

BEHAVIOUR  stlc PATH
  valid    → exit 0,   canonical rendering on stdout
  invalid  → exit ≠ 0, stdout empty, diagnostic on stderr
  missing  → exit ≠ 0

LAWS
  deterministic   same input → same bytes out
  idempotent      stlc (stlc P) = stlc P
```

## stderr is not for display

The diagnostic is prefixed with the input path. A caller that feeds the compiler a
server-side temporary file would be leaking that path by echoing stderr to a user. The exit
code is the signal; stderr is for logs.

## Output is a single line

`renderProgram` joins definitions with spaces, so a three-line input comes back as one line.
That is the current contract, not an accident of formatting — a consumer that wants one
definition per line cannot get there without parsing, so changing it is a decision for this
repo, and a change to the contract.

## Who checks what

The laws above are exercised from both sides. This repo runs its own golden test over
`Demo/`, and — before publishing — the contract suite belonging to the consumer
([LambdaLab-web](https://github.com/WegmannDavid/LambdaLab-web)), against the freshly built
binary. A compiler change that breaks the interface therefore fails here, before anything
ships, rather than in the consumer's pipeline afterwards.

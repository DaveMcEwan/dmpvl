
# Background

## `diff` and `patch`
- Basis for all version control systems discussed today.
- POSIX since X/Open Portability Guide Issue 4 (1992).
- `diff` takes file1+file2, reports their differences in a patchfile.
- A patchfile precisely describes differences between two files.
  - Most common modern format is "unified" (vs "ed", "context").
  - Some context is often required.
  - Differences are identified line-by-line.
- `patch` takes a file+patchfile, applies the differences in-place.
- Inputs must be vaguely similar.

Garbage in, garbage out.

## RCS Overview
- <https://www.gnu.org/software/rcs/>
- 1st generation, but not obsolete!
- Current version is 5.10.1 (2022-02-02).
- Implemented as a collection of utilities (not a single exe):
  - `ci`, `co`
  - `ident`, `rcs`, `rcsclean`, `rcsdiff`, `rcsfreeze`, `rcsmerge`, `rlog`

## RCS Important Details
- Stored as separate/unmerged reverse deltas.
  - I.e. delta says how to get back to *previous* version.
  - Predecessor SCCS used forward deltas saying how to get to *next* version.
- Lock indicates that somebody *intends* to deposit a newer revision.
- Branches are on version numbers
  - Symbolic name (similar to a "tag") is a prefix shortcut.
- Concept of joining is similar to merging.
- Stamping, like `$Header$`, expands strings on checkin.
- An edit script is a patchfile.

## CVS Overview
- <https://cvs.nongnu.org/>
- 2nd generation, mostly obsolete.
- Frontend to RCS which adds a client/server model.
- Centralised repository, usually accessed over RSH (predecessor to SSH).
- Composed of fewer executables (`cvs`, `cvspserver`).
- Delta compression distinguishes between text and binary.
- A "project" is a set of related files.
- Introduced "loginfo" similar to git's hooks.

## SVN Overview
- <https://subversion.apache.org/>
- 2nd generation, mostly obsolete.
- Intended to be successor to CVS, and mostly compatible.
- Many implementations of both clients and servers.
- Centralised repository, accessed over SSH, HTTP, or HTTPS
- Atomic commits to multiple files.
- Properties (key/value pairs) expand the concept of stamping.
- The SVN tool itself is version controlled
  - There are incompatibilities between versions (and that's ok).
- Relies heavily on conventions (trunk, branches, tags) so it's easy to make
  a mess.
- GUIs are all 3rd-party.

## Git Overview
- <https://git-scm.com/>
- 3rd/current generation.
- Implemented as a single executable (`git`).
- Distributed network of repositories, accessed over SSH or HTTPS.
- Designed to support development of Linux kernel.
  - Thousands of developers, distributed globally, with restrictions on network
    access, on all sorts of operating systems.
- Every repository has a full copy of history.
- Concepts of branches and tags are first-class citizens with precise
  definitions.
- GUIs provided in standard distribution, but many 3rd-party tools exist.
- Locking concept doesn't translate well.
  - Close, but slightly different, approximations can be emulated via hooks,
    branches, and talking to each other.

## Git Commits
- Each commit has a unique SHA1 hash.
- Concept of version numbering is intentionally avoided.
- Concept of stamping, like `$Header$`, doesn't exist.
  - Behaviour can be emulated via tags and hooks.
- Tags can be any format you like (please use SemVer).
  - "lightweight" tag is a convenient alias for a commit hash.
  - "annotated" tag is an object in its own right with a checksum, tag message,
    tagger's name, date, GPG signature.
  - In the same way as branches, tags must be pushed individually.
- Branches are fast, much more convenient than SVN and its predecessors.

## Git Hooks
- Run scripts on your local repo on specific events.
- Local events: `pre-commit`, `commit-msg`, `post-merge`, `pre-push`,
  and more ...
- Remote/server events: `pre-receive`, `update`, `post-receive`
- Must be setup per repository.

## SemVer and SemVerSoC
- <https://semver.org/>
- `<major>.<minor>.<patch>-<pre-release>+<build>`
- Version numbers and the way they change have convey well-defined meaning -
  that tools can rely on.
- Used for many/most open-source projects.
- ...See the tiny webpage...
- Releases may use [SemVerSoC](https://davemcewan.github.io/SemVerSoC/).

## CI/CD
- CI: Continuous Integration
  - Run regression on specific events, and complain (loudly, via email)
    if something is broken.
  - "Push branch X", "Commit to branch Y", "Every Monday at 1200"
  - GitHub has [Actions](https://docs.github.com/en/actions).
  - Great for anything code-based.
- CD: Continous Deployment
  - If the new version passes regression, then deploy it.
  - Can be built into CI flow.
  - GitHub has [Dependabot](https://github.com/dependabot).
  - Great for web development, but not for hardware or critical software.

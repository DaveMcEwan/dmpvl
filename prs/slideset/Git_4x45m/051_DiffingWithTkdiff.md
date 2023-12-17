
## Diffing with `tkdiff` 1of1
- Let's introduce a harmless change to a tracked file.
  - `echo '## HARMLESS' >> src/reuse/lint.py`
  - `git difftool`
- We can also use `tkdiff` to diff over branches.
  - `F=src/reuse/lint.py`
  - `B1=origin/master`
  - `B2=origin/summary-help`
  - `git difftool $B1:$F $B2:$F`
- First argument is LHS, second argument is RHS.
- Use `n` and `p` to move quickly to next and previous changes.
- See the documentation for all the ways you can diff.
  - <https://git-scm.com/docs/git-diff>
  - <https://git-scm.com/docs/git-difftool>

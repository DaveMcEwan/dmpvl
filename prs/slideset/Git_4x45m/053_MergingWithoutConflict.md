
## Merging Without Conflict(s) 1of3
- This is also a simple kind of merge, where the completely different changes
  have been made on converging branches.
- First, let's get back to a known state and make a change on one branch.
  - `git checkout master`
  - `git reset --hard`
  - `git checkout -b myBranchC`
  - `echo '## foo' >> README.md`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Alice.'`

## Merging Without Conflict(s) 2of3
- Second, get back to a known state and make a different change on another
  branch.
  - `git checkout master`
  - `git reset --hard`
  - `git checkout -b myBranchD`
  - `echo '## foo' >> Makefile`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Bob.'`

## Merging Without Conflict(s) 3of3
- To start the merge, first switch to the "destination" branch, i.e. the one
  that will still be worked upon.
  Let's choose to merge `myBranchD` into `myBranchC`.
  - `git checkout myBranchC`
  - `git status`
  - `git merge myBranchD`
  - Save and quit the editor
- Now, have a look at the history with `git log` and/or `gitk`.



## Merging Without Changes 1of3
- This is the simplest kind of merge, where the same changes have been made on
  converging branches.
- First, let's get back to a known state and make a change on one branch.
  - `git checkout master`
  - `git reset --hard`
  - `git checkout -b myBranchA`
  - `echo '## foo' >> README.md`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Alice.'`

## Merging Without Changes 2of3
- Second, get back to a known state and make the same change on another branch.
  - `git checkout master`
  - `git reset --hard`
  - `git checkout -b myBranchB`
  - `echo '## foo' >> README.md`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Bob.'`

## Merging Without Changes 3of3
- Now that our changes are commited, we can freely switch branches without
  losing work.
  - `git checkout myBranchA`
  - `git checkout master`
- To start the merge, first switch to the "destination" branch, i.e. the one
  that will still be worked upon.
  Let's choose to merge `myBranchA` into `myBranchB`.
  - `git checkout myBranchB`
  - `git status`
  - `git merge myBranchA`
  - Save and quit the editor
- Now, have a look at the history with `git log` and/or `gitk`.


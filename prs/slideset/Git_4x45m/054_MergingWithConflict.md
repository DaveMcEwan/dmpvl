
## Merging With Conflict(s) 1of4
- This is the usual kind of merge, where the same changes have been made on
  converging branches.
- First, let's get back to a known state and make a change on one branch.
  - `git checkout master`
  - `git reset --hard`
  - `git checkout -b myBranchE`
  - `echo '## foo' >> README.md`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Alice.'`

## Merging With Conflict(s) 2of4
- Second, get back to a known state and make a conflicting change on another
  branch.
  - `git checkout master`
  - `git reset --hard`
  - `git checkout -b myBranchF`
  - `echo '## bar' >> README.md`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Bob.'`

## Merging With Conflict(s) 3of4
- To start the merge, first switch to the "destination" branch, i.e. the one
  that will still be worked upon.
  Let's choose to merge `myBranchE` into `myBranchF`.
  - `git checkout myBranchF`
  - `git status`
  - `git merge myBranchE`
  - ... This needs some attention.

## Merging With Conflict(s) 4of4
- Look at the conflicts with `git gui`.
- Search for conflicts with `<<<<<<<`, `=======`, and `>>>>>>>`.
  - That's 7 characters for each kind of conflict marker.
- The format is always the same.
  - Conflicts are marked beginning with `<<<<<<<` (opening chevrons).
    and ending with `>>>>>>>` (closing chevrons).
  - Each conflict has two parts, partitioned by `=======` (the separator).
  - Lines outside of chevrons belongs to the most recent common ancestor
    (`master`).
  - First, lines between the opening chevrons and the separator are from the
    current/destination branch (`myBranchF`)
  - Second, lines between the separator and the closing chevrons are from the
    branch we want to merge in (`myBranchE`).
- Edit the file, commit, then look at the history.
- A simple strategy is to accept the "remote" version, then make edits, stage,
  then commit.



## Merge Using `kdiff3` 1of3
- Let's repeat the previous example, but use a GUI tool for the merge step.
  - `git checkout master`
  - `git reset --hard`
  - `git checkout -b myBranchG`
  - `echo '## foo' >> README.md`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Alice.'`
  - `git checkout master`
  - `git checkout -b myBranchH`
  - `echo '## bar' >> README.md`
  - `git add !$`
  - `git commit -m 'Add foo comment, by Bob.'`

## Merge Using `kdiff3` 2of3
- To start the merge, first switch to the "destination" branch, i.e. the one
  that will still be worked upon.
  - `git checkout myBranchG`
  - `git status`
  - `git merge myBranchH`
  - `git mergetool`

## Merge Using `kdiff3` 3of3
- There are 4 panes.
  - Left (Base) is the most recent common ancestor.
  - Middle (Local) is the current/destination branch (`myBranchG`)
  - Right (Remote) is the branch we want to merge in (`myBranchH`)
  - Bottom is the output of the merge.
- Controls and keyboard shortcuts are well described and intuitive.
- Right-click on conflicts in the bottom pane to select between solutions.
- You can type in the bottom pane.
- Save the output, then use `git gui` to view your changes as usual.


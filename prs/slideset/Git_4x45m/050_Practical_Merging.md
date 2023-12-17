
# Practical/Interactive: Git Merging

## Outline
- Preliminaries
- Example 1: Diffing with tkdiff.
- Example 2: Merging without change.
- Example 3: Merging without conflict.
- Example 4: Merging with conflict.
- Example 5: Merging with kdiff3.

## Preliminaries
1. Examples with FSF's `reuse-tool`.
2. Non-merge vs merge commits.
3. GUIs.
4. Stashing.
5. `reset` vs `revert`.
6. Commit message format.
7. `fetch`, `merge`, `rebase`, and `pull`.
8. Nordic's BitBucket branch naming scheme.

## Preliminary 1of7: Examples with FSF's `reuse-tool`
- Create a new directory to work on the repository.
  - `cd VCG/afternoon/`
  - `git clone https://github.com/fsfe/reuse-tool.git`
  - `cd reuse-tool`
- Now we can see some history.
  - `git log`
- As well as the branches and remotes.
  - `git branch`
  - `git remote -v`
  - `git branch -a`

## Preliminary 2of7: Non-Merge vs Merge Commits
- There two types of commits in Git: non-merge, and merge.
- Non-merge commits are the usual kind.
  - Extend a branch's history.
  - Single ancestor.
  - Must contain differences.
  - Created with `git commit`.
- Merge commits join two branch's histories.
  - Two ancestors.
  - *May* contain differences.
  - Created with `git merge`.
- Have a look at merge commits: `git log`
  - A merge commit with no differences: `git show 95b6dd09`
  - A merge commit with differences: `git show 65b3206a`

## Preliminary 3of7: GUIs
- CLI will give you canonical status/results, but GUIs can make some tasks
  easier.
- `git status`: Visualise status with `git gui`.
  - In the default distribution.
  - Also useful for amending the previous commit.
- `git log`: Visualise branch history with `gitk --all`.
  - In the default distribution.
- `git diff`: Navigate diffs one file at a time with `git difftool`.
  - `git config --global diff.tool tkdiff`
- `git merge`: Resolve conflicts with `git mergetool`.
  - `git config --global merge.tool kdiff3`

Note: `--global` changes `~/.gitconfig`, instead of `./.git/config`

## Preliminary 4of7: Stashing
- A handy tool for digging yourself out of a mess.
- Save uncommited and unstaged changes temporarily.
- Easier than saving files to temporary locations.
- Implemented as a stack.
  - Push unstaged changes with `git stash`
  - Pop with `git stash pop`
- Let's try that quickly by making a change, then attempting to pull.
  - `echo BREAKTHINGS >> ./README.md`
  - `git pull --rebase`
- For a rebasing pull to succeed, tracked files must be unmodified.
  Save our change onto the stash stack.
  - `git stash`
  - `git pull --rebase`
- Now we can get our change back.
  - `git stash pop`

## Preliminary 5of7: `reset` vs `revert`
- To undo unwanted changes that aren't commited, reset all tracked files.
  - `git reset --hard`
- That puts your working repo back to `HEAD`.
- To undo changes made by existing commits, we need a new commit which
  reverses the diff.
  - `git revert <commit>`
- To help yourself and colleagues:
  - Write useful commit messages in the de-facto standard form.
  - Use searchable keywords in commit messages.
  - Review the diff before you make each commit.
  - Keep unrelated changes in separate commits.

## Preliminary 6of7: Commit Message Format
- De-facto format supported by GitLab, BitBucket, GitHub, 3rd-party tools, etc.
- First line is a subject, up to 50 characters.
- Second line is empty/blank.
- Subsequent lines are the body, up to 72 characters.
- Subject is in imperitive mood, i.e. commanding.
  - Good: "_Add_ support for Foo."
  - Bad: "_Adds_ support for Foo."
- Alternatively, if the commit is very simple and doesn't need a body, word
  the subject as a phrasal noun.
  - "Foo support"
- Both subject and body should be formatted in
  [Markdown](https://commonmark.org/).

## Preliminary 7of7: Fetch, Merge, Rebase, and Pull
- `git fetch`: Fetch/copy the newest branch and commit data from a remote, but
  don't change any branches or working files.
- `git merge`: Performs a 3-way merge between two branches and their most recent
  common ancestor.
- `git rebase`: Take the series of commit patches and apply them to rewrite the
  branch's history.
  - Rewriting history is not allowed on some server setups.
    In those systems, you'll rarely (if ever) use the rebase command.
- `git pull`: Execute `git fetch` then `git merge` (or `git rebase`).
  - If you're unsure, use separate steps for fetching and merging.


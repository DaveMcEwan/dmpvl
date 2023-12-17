
## Git 1of11
- Objective 1: Feel familiar with inspecting the system.
- Objective 2: Be comfortable starting a new repository.
- Estimated time: 30 minutes.
- Follows then extends what we just did with RCS.

## Git 2of11
Let's start by making a couple of files to play with...

- `cd VCG/morningGit/`
- `printf 'hello\nworld\n' > foo.txt`
- `printf 'red\nblue\n' > bar.txt`
- `ls -al`

... and initialising the repository.

- `git init`

## Git 3of11
Let's have a look what that did to our workspace.

- `find . | sort`

Immediately noticable is that the management structure looks more like a
database.
Git commands mostly work on these files, so let's see an example of that
with `.git/config`.

- `cat .git/config` and/or `git config user.name`
- `git config user.name "Sam Smith"`
- `cat .git/config` and/or `git config user.name`

## Git 4of11
Next, let's tell git to manage our files.
This has two steps (add to the staging area, then the atomic commit).

- `git add foo.txt bar.txt`
- `git commit -m 'Little message about the changes.'`

Also different from RCS is that we can always edit our working files.

- `echo writableYes >> foo.txt`

## Git 5of11
We can see changes between the working directory and the staging area (also
known as the cache).

- `git diff`

And changes between the staging area and the commited files.

- `git add foo.txt`
- `git diff --cached`

## Git 6of11
The actions of tracking files and viewing differences between revisions in Git
are immediately comparable to RCS.

- Can see exactly what is meant by atomicity?
- Can you see how things are arranged in your local workspace?

## Git 7of11
Now let's have a look at the distributed and decentralised features.
Create a *bare* repository that can work like GitLab/BitBucket/GitHub, then
have a look inside.
Do this somewhere else on the filesystem - not in the repo you've just created.

- `cd VCG/morningSomewhereElse/`
- `git init --bare MyRepo`
- `ls MyRepo/`

## Git 8of11
Back in our original repo, we can add that as a remote for our original.
We're using the name `myremote`, but BitBucket and GitHub suggest the name
`origin` in their documentation.
You can use whatever alias you like - it's your choice and doesn't affect
anybody else.

- `cd VCG/morningGit/`
- `git remote add myremote path/to/MyRepo`

Note that this does nothing to MyRepo yet.
When we push our original repo, that's when the network access occurs.

- `git push myremote master`

Now have a look around MyRepo where you can see that the contents
of `objects/` is identical to those in our local copy.
You can add as many remotes as you like, name them however you like, and
synchronise them however you like.

## Git 9of11
To see a nice overview, you can use the standard GUIs for working with local
changes and seeing what your local repo knows about other repos.
Let's have a quick look now.
Both `git gui` and `gitk`, implemented in Tcl/Tk, are included in the usual
distributions of Git and provide a consistent interface on Linux, BSDs, MacOS,
and Windows.

- `git gui &`
- `gitk --all &`

## Git 10of11
Finally, let's play with a merge which has a little conflict.
Merging the changes from a branch in your local repo is the same process
as merging the changes from a branch on a remote repo - just fetch first.

- `git checkout -b firstBranch`
- `echo apples >> foo.txt && git add . && git commit -m 'Add apples.'`
- `git checkout master && git checkout -b secondBranch`
- `echo oranges >> foo.txt && git add . && git commit -m 'Add oranges.'`

Finally, return our working directory to the HEAD of `master`.

- `git checkout master`


## Git 11of11
We'll try merging the first branch, then the second.

- `git merge firstBranch`
- `git merge secondBranch`

That didn't work because, in the second merge, changes had been made to the
same part of the file touched by a commit since their common ancestor.
We could also have made this conflict by adding the "apples" line directly
on the `master` branch.

To fix the conflict, we need to choose what is right.
The simplest way to do this is to accept either change using `git gui`,
then modify it manually before the merge is committed.
We'll go over different ways of merging in the afternoon.

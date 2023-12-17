
## RCS 1of4
- Objective 1: Feel familiar with inspecting the system.
- Objective 2: Give a point of comparison against git.
- Estimated time: 10 minutes.
- There's a similar tutorial here: <https://www.madboa.com/geek/rcs/>

## RCS 2of4
Let's start by making a couple of files to play with.

- `cd VCG/morningRCS/`
- `printf 'hello\nworld\n' > foo.txt`
- `printf 'red\nblue\n' > bar.txt`
- `ls -al ./ RCS/`

And provide a place for RCS to keep its data.

- `mkdir RCS`

## RCS 3of4
Next, let's tell RCS to manage these files.
By default, RCS will delete the original files on checkin, so you usually
want the `-u` option to keep them in the working directory.

- `ci -u foo.txt bar.txt`
- `ls -al ./ RCS/`
- `cat RCS/foo.txt,v`

## RCS 4of4
Now, let's try making a change to `foo.txt`

- `echo writableNo >> foo.txt`

But wait! You need to checkout first.

- `co -l foo.txt`
- `echo writableYes >> foo.txt`
- `ls -al ./ RCS/`

And finally, we can observe that we've made changes.

- `rcsdiff`



## Background and Motivation
- Dave McEwan, currently working at Codasip
- Talking about the open source SystemVerilog linting tool that I've been
  contributing to for a couple of years.
- 15s : 0m0s .. 0m15s

### What is SystemVerilog?
- First, let's quickly cover what SystemVerilog actually is.
- It's a formal language usually used for describing hardware logic systems,
  and for verifying those systems.
- I say "a" language, but it's arguably 2: a text pre-processing language,
  and the main language for describing event-based logic.
- The preprocessor is only vaguely described in the language reference manual.
  That's why every tool's preprocessor is different.
- And the main language is described with a formal grammar, BNF.
- As with any formal language, there's good code and bad code, and everybody's
  opinion is different.
- 45s : 0m15s .. 1m00s

### What is svlint?
- Svlint is a command-line tool to do basic analysis on SystemVerilog code.
- It's open-source, MIT licensed, developed on GitHub, written in Rust,
  originally by a Japanese guy, the codebase is beautifully structured, and
  it's easy to install.
- It's also very fast, because the type of analysis it does is simpler than
  commercial heavyweights that require licenses, but still quite powerful.
- I'll talk a bit about what you can do with in in a minute, but first, what is
  a linter.
- 35s : 1m00s .. 1m35s

### What is a linter?
- I'm just going to read this statement, because I can't think of a better
  description!
- A linter is a tool which classifies pieces of code as allowed or
  forbidden according to a set of precise rules.
- So, without lint checks, every feature of the language is allowed, but
  whether your tools support those features is another matter.
- For whichever set of people you work with, and tools you use, you need to
  know what works and what doesn't, for you.
- That extends all the way from things like compiler errors to the way your
  team does code reviews.
- Now, specifically for SystemVerilog, there are different points in toolflows
  where you can perform these checks...
- 55s : 1m35s .. 2m30s

## Operation

### Levels of SystemVerilog Analysis
- ...before the preprocessor, in a parser, in compilation of a single module,
  elaboration combining multiple modules, in simulation, and so on.
- Svlint works only at two points, on the text before the preprocessor, and
  on the syntax tree emitted from the parser.
- That means it doesn't know anything about wrongly driven signals, or
  unconnected ports, or X-propagation, or any of those higher-level concepts.
- So without all those things, what's the point?
- You can save quite a bit of time, if you can be sure of certain
  things before wasting time in a code review.
- Things like
  - naming conventions are followed
  - not using incompatible features, perhaps `interface`s
  - no verif-only features in design code, like `task`s
  - no dangerous constructs, like mixed-up blocking/non-blocking statements,
    case without a default arm, etc.
- If have access to expensive tools anyway, it's also nicer if you don't waste
  licenses performing these very basic checks - make these tools work for their
  money!
- 75s : 2m30s .. 3m45s

### How svlint works
- Svlint works quite simply.
- First, it iterates over source lines, checking each line in turn.
  This is effectively like a fancy grep.
- Next, the source is preprocessed then parsed to form a syntax tree.
- And last, it iterates over the syntax tree, checking each node in turn.
- Importantly, the rules are pass/fail, with no intermediate levels like
  warning or anything, and only violations are reported.
- 40s : 3m45s .. 4m25s

### Examples of Text and Syntax Rules
- This is only a short presentation, so I'm not going into too much detail
  of all the available rules, but heres a small selection.
- The 2 text ones do as their names suggest, checking that lines are less than
  a specified length, and that there's a copyright notice at the top of the
  file.
- There's a syntax rule to detect blocking assignments in a place you typically
  don't want them.
- Another to check that constants don't contain Xs or Zs.
- There are around 20 rules for checking whitespace, all beginning with
  "style".
- And here are 3 rules related to the naming of input ports.
  The regex ones are more complicated, so there's an alternative simple one
  just for convenience.
  Yes, if you really want you can use the regex `.*` to forbid any input port
  from being declared!
- 60s : 4m25s .. 5m25s

### Rulesets
- Sometimes it's difficult to work out how to forbid something dangerous,
  without getting in the way of useful code.
- That means it could be difficult for a newcomer to figure out which of the
  100 or so rules they should enable, so there are about 10 rulesets you can
  use out of the box.
- The names should be fairly self-explanatory, and the effects of each one are
  detailed in the manual.
- If you don't like anything in them, you can just use them as a starting
  point, and if your ruleset is worth sharing, just open an issue or pull
  request on GitHub.
- Practically, a ruleset is just a TOML configuration file that you use with
  the environment variable `SVLINT_CONFIG`.
- 45s : 5m25s .. 6m10s

### Wrapper Scripts
- To use those bundled rulesets, you could use something like environment
  modules, or you can use the bundled wrapper scripts.
- Those just give you executable scripts with short convenient names in the
  same directory as the main binary.
- If you want to do additional stuff, perhaps updating a database or
  interacting with Jira, you can add that stuff in the wrapper scripts.
- Again, if you have functionallity that's worth sharing, please do.
- 30s : 6m10s .. 6m40s

### Text-Editor Integration
- The last feature I want to talk about is how you can use svlint while you're
  actually editing code.
- There's an additional component called svls, that speaks the Language Server
  Protocol, which most text editors support.
- Even if you've never heard of it, you've probably used it when you see your
  IDE gives you hints about syntax errors and suggests corrections.
- The protocol is quite large, and only a minimal set of features are
  implemented, so things like go-to-definition are not supported by svls.
- Things like that are served by other tools.
  Svls is only about integrating svlint with your text editor.
- We'll come to some screenshots in a minute.
- 45s : 6m40s .. 7m25s

## Illustrations

### Sources
- Before we see the screenshots, let's just see the exact code we're analysing.
- The first one is an obvious syntax error, woops instead of `always`.
  That means the module cannot be successfully parsed from text into a syntax
  tree.
- The second has a blocking statement in the `always_ff` process.
  This module can be parsed but it could cause a mismatch between what you see
  in simulation and what your synthesis tool thinks the hardware should do.
  That carries the risk of our silicon being non-functional, so that fails our
  checks.
- The last one is what we actually want.
  It won't compile because we haven't declared `clk` or `z`, but that's not
  actually required to be valid SystemVerilog syntax!
- 50s : 7m25s .. 8m15s

### Command Line svlint-simsynth
- This is what you'd expect to see when you run svlint.
- The exit code is 0 if there are no problems, and 1 if there is a problem.
- Each rule violation is reported with a hint that tells you *what* to do, and
  a reason that tells you *why* the rule exists.
- 20s : 8m15s .. 8m35s

### Vim with vim-lsp Plugin
- I'm a fan of Vim and working mostly in the terminal, so here's what that
  looks like with my garish colourscheme.
- Errors in the preprocessor or parser are shown as errors, and rule violations
  are shown as warnings with their hints.
- 20s : 8m35s .. 8m55s

### VSCode
- For people that prefer their editors to be a bit more GUI, here's what that
  looks like in VSCode, using the svls-vscode extension from the normal
  marketplace.
- Preprocessor and parser errors are underlined red, rule violations are
  underlined yellow(?), the PROBLEMS pane shows you the hint telling you what
  to do, but not the reason.
- 30s : 8m55s .. 9m25s

## Thanks for Listening. Questions?
- In summary, it's a easy-to-use free tool that helps you check your code for
  obvious mistakes.
- It's not my project, but I've done a lot of contributions.
- If you'd like more information, you can check it out on GitHub.
- There's plenty of detail in the manual, and I think these slides will be
  distributed afterwards.
- Or just say hi after the presentations.

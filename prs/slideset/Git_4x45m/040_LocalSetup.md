
# Local Setup

## Outline
- GitLab, BitBucket, GitHub
- SemVer and SemVerSoC
- Jenkins
- Q and A

## GitLab, BitBucket, GitHub
- Hooks may prevent rewriting history, like amending pushed commits.
- Hooks may enforce branch our naming scheme.
- Markdown is rendered on all web views.
  - README, commit messages, pull requests
- PDF is also viewable in the web browser, but not DOCX.
- SVG,PNG,JPG are rendered, but not VSDX.
  - SVG can be diffed -- [Inkscape](https://inkscape.org/) is recommended for
    most diagrams and [Wavedrom](https://wavedrom.com/) for waveforms.
  - Visio obfuscates SVG!

## Git Submodules
- Incorporate other git repositories into your repository.

## SemVer and SemVerSoC
- [SemVer](https://semver.org/) ascribes meaning to software version numbers.
- [SemVerSoC](https://davemcewan.github.io/SemVerSoC/) clarifies SemVer's rules
  for HDL/RTL projects.
- You've probably used SemVer constraint solvers before - in package managers
  like `apt` (Debian), `rpm` (RHEL/CentOS), `cargo` (Rust), `pip` (Python).

## Jenkins
- <https://github.com/jenkinsci>
- A continuous integration tool.
- Free, open-source software written in Java.

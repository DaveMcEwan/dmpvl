
Usecases for consistent style.
- Within a team developing a components, consistency helps team members
  transition quickly between components.
  It doesn't really matter exactly what style is chosen, just that it's
  consistent, because any style will feel familiar/comfortable after some use.
- Compatibility between a wide variety of tools.
  Look and feel aspects don't matter much, but particular syntactic features
  are very important.
  The chosen style must have compatible semantics as interpreted by all tools,
  including tools we might not know about yet!
  That means the style must be crafted with some understanding of how future
  tools are likely to work and anticipate their problems.
- Design review.
  - Code should match diagram.
    That's some redundancy to protect against programming errors.
  - Visual noise should be minimized so that anything "special" sticks out and
    invites extra scrutiny.
- Verif review.
  - Where exactly are probes connected? Whitebox/blackbox?
- Integration.
  - Need to read a *lot* of files quickly and be able to extract key
    information.
  - Integrator's perspective is like a fast-paced lightweight design review.
- FAE/QRF tackling urgent customer problems.
  - Need to understand many parts of a system which are usually thought of as
    unrelated.
- Portability between platforms.
  - Will the system behave the same on a simulator, emulator, FPGA, and ASIC?
  - How do you run checks like design assertions?

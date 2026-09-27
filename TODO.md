# TODO

- We should probably have a way to configure the `softcore!` macro to allow
  non-deterministically changing part of the spec which is not declared as part
  of the clobber. What are the actual thing we are clobbering, and what are the
  CSRs which do not need to be touched? This is actually an interesting
  question. In FunTAL, they are kinda specifying EVERYTHING in the type-system,
  but this seems kinda too overkill


# discussion

  - merge `fun` and `rec`?
    (with a way to refer to the previous identifier with the same name)

## type inference
  - partial outcome? (i.e. with a part that is inferred)
    e.g. bst.mome

## loops
  - `loop` with a call before the defn?
    `where loop`?

  - mutually recursive loops?
      would mean the same outcomes

    rec loop a = ...
    and loop b = ...
    and      c = ...

  - for loops

    - over integers `for i in lo..hi`
        syntax for `for i in range(lo, hi)`
        `i` available in invariant (as `lo + len seen`)
        automatic invariant `lo <= i <= hi` is added
        as in Why3, two cases for `lo > hi` and `lo <= hi`

      Rust has syntax `lo..=hi` to include `hi`

      syntax for decreasing sequence?
      principle: describe the interval + the way it is iterated over
      (increasing/decreasing / by 1/-1/etc.)

    - general case `for x in c`
        `seen` (sequence of produced elements) available in invariant

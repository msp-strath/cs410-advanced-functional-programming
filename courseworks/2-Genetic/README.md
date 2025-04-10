# Installing dependencies

## `random`

Note that `System.Random` is ultimately using Haskell functions
to implement the `IO` randomness. To compile the project, you'll
need to have the Haskell `random` library installed. It should
be possible to do it by invoking the following command from the
terminal:

```shell
cabal install --lib random
```


## `text`

Similarly, the `String` manipulating primitives are implemented
in terms of Haskell functions and so you will need `text` installed.
It should be possible to do it by invoking the following command
from the terminal:

``shell
cabal install --lib text
```

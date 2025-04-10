# Installing dependencies

Note that `System.Random` is ultimately using Haskell functions
to implement the `IO` randomness. To compile the project, you'll
need to have the Haskell `random` library installed. It should
be possible to do it by invoking the following command from the
terminal:

```shell
cabal install --lib random
```

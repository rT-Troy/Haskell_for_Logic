## Haskell Project of Logic


```cabal install split```


### Testing

#### Testing by stack
```
stack test

stack test --coverage
```

#### Testing by cabal
```
cabal test

cabal test --enable-coverage --disable-library-coverage
```

### Documentation

```
stack haddock
```

cabal will generate documentation during ```cabal build```.

### Generate github CI

```
haskell-ci github logichaskell.cabal
```
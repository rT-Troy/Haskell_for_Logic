## Haskell Project of Logic


```cabal install split```


### Testing


[Calculator](https://www.wolframalpha.com/)
```
and  or  implies  iff 
convert (A implies (B implies C)) to CNF
```

https://www.erpelstolz.at/gateway/formular-uk-zentral.html

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
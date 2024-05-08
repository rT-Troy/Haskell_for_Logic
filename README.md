## Haskell Project of Logic


### Documentation

cabal will auto-generate documentation during ```cabal build```.
```
stack haddock
```



### Testing
There are two calculator for proving the correctness.

[Online Calculator](https://www.erpelstolz.at/gateway/formular-uk-zentral.html)


[Calculator](https://www.wolframalpha.com/)
```
and  or  implies  iff 
convert (A implies (B implies C)) to CNF
```

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
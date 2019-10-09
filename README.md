# Featherweight Generic Go Generator

Featherweight Go (FG) is a small but significant subset of the Go programming language.
Featherweight Generic Go (FGG) is an extension of FG with generics.
This project is an enumerator for well-typed FGG programs, to enable the property-based testing of implementations of Generic Go.

There are a couple of restrictions to this FGG generator.
Go and FGG are languages with many n-ary constructs – structs can have many fields, interfaces can have many fields, methods can have many arguments, and in FGG each of these can  have any number of type parameters as well!
The generator generates a subset of FGG in which each of these n-ary constructs can have *zero*, *one*, or *two* instances.
This is largely to cut down on the number of generated terms.

The ‘Main.hs‘ file included in this package simply enumerates all well-typed FGG programs with up to 10 constructs.
However, it should be fairly simple to provide your own program which *uses* the generated constructs, based on the example given.

Compilation and installation should be easy.
Make sure you have an up-to-date version of [Haskell Stack](https://docs.haskellstack.org/en/stable/README/).
Then you can use the following commands:

``` bash
$ stack build    # builds the project
$ stack install  # installs the executable generated from Main.hs
$ stack run main # runs Main.hs
```

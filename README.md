# A Few Generic Go Programs

We use @claessen2105 to lazily enumerate all well-typed programs from a subset of FGG up to some size.
The subset is made up of those programs where:
+ the program has *at least* one method and one field;
+ the program has *at most* one empty interface and *at most* two empty structs;
+ each method has *at most* two arguments;
+ each struct has *at most* two fields;
+ each interface has *at most* two members and two parents; and
+ each method or type constructor has *at most* to type parameters.
Moreover, we disallow mutually recursive type definitions.
These measures are taken in an effort to truncate the space of possible programs.

---

Koen Claessen, Jonas Duregård, and Michał Pałka.
*Generating constrained random data with uniform distribution.*
Journal of Functional Programming, 2015.

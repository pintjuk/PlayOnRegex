## About
I this project an implementation of marked regular expressions is modeled in HOL to verify the correctness of the model.
This project also provides an regexp library for SML that utilizes SML code generated from the verified model.

We base our implementation on a description of how marked regular expressions can be implemented in haskell in the paper: A Play on Regular Expressions by Sebastian Fischer,
Frank Huch and Thomas Wilke published as a functional pearl at ICFP 2010 (http://www-ps.
informatik.uni-kiel.de/~sebf/pub/regexp-play.html)


The benefit of marked regex is that no determinization needs to be performed, and rung time for matching a word is O(log(m)n) where m is size of the regex and n is the size of the word.

matching using DFA is O(n), however constructing a DFA from regex takes exponential time in the size of the regex.

Our testing against regexpMatch.sml library confirms this. and illustrates the benefit.

## How to use marked regex sml library

### Regexp syntax:

```SML
Eps
```

matches empty word

```SML
Sym #"c"
```

matches "c"

```SML
Sym 10
```

matches word [10]

```SML
Alt a b
```

like "a|b", matches if a or b match

```SML
Seq a b
```

concatenation of regexes a and b, like "ab"

```SML
Rep r
```

repeat r 0 or more times like "r*"

```SML
rep_n n r
```

repeat regex r n times

```SML
$"foobar"
```

regex that matches "foobar" exactly 


### Some functions

```SML
match_marked regex word
```

match_marked  checks if regex accepts the word, where word is a list with free element type. returns a boolean

```SML
smatch_marked regex string
```

convenience method for matching strings. for example: 


## What is verified

the following is a high level definition of the language of regular expresions, that is all the lists a regeular expresion accepts.

```SML
 val language_of_def = Define
  `(language_of Eps = {[]}) /\
   (language_of (Sym c) = {[c]}) /\
   (language_of (Alt a b) = (language_of a) UNION (language_of b) ) /\
   (language_of (Seq f s) =
     {fstPrt ++ sndPrt | (fstPrt IN language_of f) /\
                         (sndPrt IN language_of s) } ) /\
   (language_of (Rep r) =
     {x| ?words. (EVERY (\e. e IN language_of r) words) /\
                 ((FLAT words)=x)})`;
```
We have verefied in hol the corectness of of marked regex implementation in HOL by proving the following lemma:

> !r w. accept_m (mark r) w <=> w IN (language_of r)

This lemma states that our marked regex model given a regex, accepts exactly thoughs strings in the language of the regex (as defined by our high level definition of the language of a regex).

## Testing

We preformed some tests against the 
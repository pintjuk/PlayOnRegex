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


### How to build

1) Install polyML
2) follow HOL documentation to clone and build HOL
3) Run ``` Holmake all ``` in this projects directory

#### To run tests and see results

```bash
Holmake selftest.exe
./selftest.exe
```
## What is verified

the following is a high level definition of the language of regular expressions, that is all the lists a regular expresion accepts.

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
We have verified in HOL the correctness of of marked regex implementation in HOL by proving the following lemma:

```SML
!r w. accept_m (mark r) w <=> w IN (language_of r)
```

This lemma simply states that our model of marked regexp is consistent with our high level definition of the language of regular expressions.

More precisely it states that marked regular expresion, given a regex, accept only thous words in the language of the given regular expresion as defined above.

## Testing

We preformed tests on the generated marked regex library against the a previous implementation of regex matching in the library regexpMatch.sml. This implementation is based on construction of DFA from regex.

### Regression testing

We preformed regression testing on the following regex:
```
((a|b)*c(a|b)*c)*(a|b)*
```

It accepts words in the language {a,b,c}, where c occurs an even number of times.

We performed the test by running the DFA implementation and our marked regex library on randomly generated words in the language  {a,b,c} and comparing results. Expecting the implementations to agree. We have been running up to 100 generated cases.

### Scalability testing


### Scaling size of the regex and the matched string
The draw back of the DFA implementation is that the prepossessing may take exponential time in the worst case.
First we performed scalability tests on the regex

```
(a|ε)^n (a)^n
```

matching it against strings of length n consisting of only a's


This is the result for the DFA implementation:
```
n: time(s)
1: 3.308
11: 0.000
21: 0.008
31: 0.064
41: 0.192
51: 0.448
61: 0.896
71: 1.664
81: 2.784
91: 4.768
101: 7.296
111: 11.204
121: 17.632
```

Indeed we see that the runtime almost double every time n is increased by 10.

This are the results for Marked regex implementation. we would expect it to run in n*log(n) by it runs to fast to see a trend:

```
n: time(s)
1: 24.172
11: 0.000
21: 0.000
31: 0.000
41: 0.000
51: 0.000
61: 0.000
71: 0.000
81: 0.000
91: 0.000
101: 0.000
111: 0.000
121: 0.004

```

The marked regular expression clearly dominates over the standard implementation when it comes to matching with large regular expressions.

### Scaling the matched string

When we keep the size of the regex constant and only scale up the matched string we would expect the DFA implementation to perform better. Since the preprocessing in this case become a constant amount of work, And computing the next state of the DFA is much simpler then computing the next state of a marked regex.

Indeed this is what we saw in our tests. In this tests we used the regex described above that matches words with even number of c's. And only scaled up the randomly generated words that we tested against. "n" in the following tables is the size of the word.

#### DFA implementation:
```
n: time(s)
6: 1.076
20006: 0.000
40006: 0.000
60006: 0.000
80006: 0.000
100006: 0.004
120006: 0.000
140006: 0.000
160006: 0.000
180006: 0.000
200006: 0.004
220006: 0.000
240006: 0.000
260006: 0.000
280006: 0.004
```


#### Marked regex:
```
20006: 0.000
40006: 0.008
60006: 0.016
80006: 0.016
100006: 0.024
120006: 0.028
140006: 0.040
160006: 0.040
180006: 0.048
200006: 0.060
220006: 0.060
240006: 0.076
260006: 0.068
280006: 0.080
```

As expected though the run time only grows linearly for marked regex when only the length of the word is allowed to vary.
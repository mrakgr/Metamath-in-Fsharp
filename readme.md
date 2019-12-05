Implementation of Metamath in F# for the sake of learning its internals.

Date: 12/5/2019

As by this point, I've been working on this for nearly two weeks - about a week longer than I wanted, I am putting this project on a permanent hiatus as I am way overdue on starting my studies of set theory and this side project that will never be used anyway is consuming way too much of my time. Three days ago, I had an almost working version that did the whole thing in one pass, but as the code was too hard to read, I've completely rewritten into the form that can currently be seen in `main.fsx`. It is currently untested, lacks error reporting and proof decompression. It would take a few more days of work to get it into shape.

Ignoring that the way it is currently structured is quite pleasing and it is a definitely an improvement to the one-pass compiler that came before. It might be baseless to say this as I haven't seen most of the other variants, but I would guess that this particular Metamath verifier would score high on readability.

I learned a couple of lessons from this experience.

The biggest mistake I made is that I got competitive with Python and decided to foolhardily try to beat it in lines of code. That first mistake lead to another which was trying to squeeze everything into a single pass even if the parser combinators lead to horrible code coupling. Another mistake was keeping that up for full 9 days, before switching gears.

One of the reasons why I wanted to keep everything in one pass besides speed is that I could reuse FParsec's mechanisms for error reporting, but later it turned out that FParsec was eating newlines in error message.

With regards to the language, one lesson that I've learned is that Metamath is not particularly well designed. As an example, variables are first declared and then typed in a different statement. I've seen this kind of mechanism in other languages (Smalltalk for example) and it has never not been a mistake. Indeed, in the implementation I have to check whether they are active and then whether they are floated. In fact, there are 3 different links to consider when using labels: declaration, floating, and then floating labels. Why do 1 when you can do 3?

Another issue is that despite working for it on 12 days, the disjoint variable constraint mechanism is opaque to me and I can't really see how the way it is done currently would be better than proper lexical scoping. This design decision seems like a hack more than anything. It adds a lot of complexity to the implementation of the language, and if I was the original designer I honestly would not be able to stomach either that or the various scoping shenanigans that Metamath does. Lambda calculus styled languages are really a hard hurdle to beat in terms of elegance and simplicity.

I've definitely taken Metamath simplicity too much at face value and underestimated how challenging it trully would be to implement.

Now admittedly, Metamath is more than just one language - it has been made to support various different logics as can be seen on its main page which is a strength, but in terms of both readibility and usability when it comes to theorem proving, languages like Agda beat it. Logics are eloquent when used directly, and Metamath is harsher, lower level logical assembly.

Metamath's biggest strength is its extensive library, and I am eager to dive into it. It is a frequent habit of mine to do some grunt work before starting anything new - such as studying set theory in this case.

P.S. The commit messages are extremely sparse in this repo. During this time I've been using [CFR In Fsharp](https://github.com/mrakgr/CFR-In-Fsharp) as my programming journal so more details on the developments done in this repo are available there.
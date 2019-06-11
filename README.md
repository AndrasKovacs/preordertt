### preordertt

Experiments with preordered set models of (directed) type theories.

The goal is to explore "preordered type theory", which can be viewed
as the simplest interesting version of directed type theory, where
every closed type can be modeled as a preordered set.

In preordered TT, every type comes equipped with a preordering (which
may or may not be interesting), and every construction in the TT
respects these orderings. Previous directed type theories in the
literature had intended models where closed types are categories
(1-categories or higher). In comparison to these, the standard models
of preordered TTs are greatly simplified by definitional proof
irrelevance of orderings. Preordered TT seems to be an excellent
playground to explore directed TT ideas, because formalization is
relatively easy, and we can focus on the essential polarity issues.

The "signedCxt" folder contains a formalization where context
extension is modelled similarly to Harper & Licata's [2D directed TT](https://www.cs.cmu.edu/~rwh/papers/2dtt/mfps.pdf).

The "cxt" folder has context extension is done similarly as in the
presentation by Altenkirch at [2019 Krakow TYPES
meeting](https://eutypes.cs.ru.nl/eutypes_pmwiki/uploads/Meetings/Altenkirch_slides.pdf).

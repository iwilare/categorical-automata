# Categorical automata in Agda

This repository contains the Agda formalization for a series of papers by Guido Boccali, Andrea Laretto, Fosco Loregian, Stefano Luneia and Bojana Femić on categorical automata in monoidal and cartesian (bi)categories.

- "Bicategories of automata, automata in bicategories" (https://arxiv.org/pdf/2303.03865.pdf)
- "Completeness for categories of generalized automata" (https://arxiv.org/pdf/2303.03867.pdf)
- "Semibicategories of Moore automata" (https://arxiv.org/abs/2305.00272)

## Main formalization files

- [Automata](Automata.agda) ([Moore](Moore.agda) / [Mealy](Mealy.agda)) - definition of machines as spans in a cartesian category
- [FMoore](FMoore.agda) / [FMealy](FMealy.agda) - definition of F-machines, generalizing to endofunctors in the span
- [Mealy/Bicategory](Mealy/Bicategory.agda): the bicategory of Mealy automata
- [FMoore/Limits](FMoore/Limits.agda): terminal object and products in the category of F-Moore automata
- [AsPullbacks](AsPullbacks.agda): redirection to the definition of F-Moore and F-Mealy as strict pullbacks in **Cat**
- [Set/*](Set/) main development of "Semibicategories of Moore automata", using direct computations in **Set**

## Requirements

- `agda-categories` 0.1.7.2
- `agda-stdlib` 1.7.2
- `agda` 2.6.3

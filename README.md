# The Integers as Equivalences in Homotopy Type Theory
This is the repository for the formalization accompanying [1].


## Contents of this repository
1. `GrpdHITs/`: The repository accompanying [2].
1. `Categories/`: An initial attempt to create an algebra of precategories for ℤh and ℤb.
1. `Prebicategories/`: Various notions related to prebicategories, pseudofunctors and pseudotransformations, Chapter 4 of [1].
1. `signature.v`: Definition and interpretation of polynomial codes, path and homotopy endpoints and signatures, §6.2 of [1]
1. `TypeHomot/`: The definition of the prebicategory of types and construction of algebras on them based on signatures for higher inductive types, §6.1 and §6.3 of [1].
1. `WildCategories/`: The theory of wild categories and a proof that adjunctions in them preserve initial objects, Chapter 7 of [1].
1. `Zh_Zb_sig.v`: Signatures for ℤh and ℤb, §6.4 of [1].


Each file starts with a small description of the content of the file. Large parts of this code are from GrpdHITs or the UniMath library and adapted to the prebicategorical setting. Where this is the case, the source files are mentioned.


## Installation
1. Follow the installation instructions of GrpdHITs.
1. `coq_makefile -f _CoqProject -o Makefile`
1. `make`

## Bibliography

1. Koen Timmermans, 'The Integers as Equivalences in Homotopy Type Theory'. MSc thesis at Radboud University.
1. Niccolò Veltri and Niels van der Weide, 'Constructing Higher Inductive Types as Groupoid Quotients'.

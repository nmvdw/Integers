# The Integers as Equivalences in Homotopy Type Theory
This is the repository of the formalization accompanying Koen Timmermans' MSc thesis 'The Integers as Equivalences in Homotopy Type Theory' (*). 


## Contents of this repository
1. `GrpdHITs`: The repository accompanying the paper 'Constructing Higher Inductive Types as Groupoid Quotients' by Niccolò Veltri and Niels van der Weide.
1. `Categories`: An attempt to create an algebra of precategories for ℤh and ℤb.
1. `Prebicategories`: Various notions related to prebicategories, pseudofunctors and pseudotransformations, Chapter 4 of (*).
1. `TypeHomot`: The definition of the prebicategory of types and construction of algebras on them based on signatures for higher inductive types, Chapter 6 of (*).
1. `WildCategories`: The theory of wild categories and a proof that adjunctions in them preserve initial objects, Chapter 7 of (*).

Each file starts with a small description of the content of the file. Large parts of this code are from GrpdHITs or the UniMath library and adapted to the prebicategorical setting. Where this is the case, the source files are mentioned.


## Installation
1. Follow the installation instructions of GrpdHITs.
1. `coq_makefile -f _CoqProject -o Makefile`
1. `make`

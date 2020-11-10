(* Definitions of the wild category of types *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Require Import WildCategories.WildCat.

Definition type_wild_cat : wild_cat.
Proof.
  use build_prebicat_data.
  - exact Type.
  - exact (λ X Y, X → Y).
  - exact (λ X Y f g, f ~ g).
  - exact (λ X x, x).
  - exact (λ X Y Z f g x, g (f x)).
  - exact (λ X Y f, homotrefl f).
  - exact (λ X Y f g h θ γ, homotcomp θ γ).
  - exact (λ X Y Z f g h θ, funhomotsec f θ).
  - exact (λ X Y Z f g h θ, homotfun θ h).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y Z W f g h x, idpath (h (g (f x)))).
  - exact (λ X Y Z W f g h x, idpath (h (g (f x)))).
Defined.



/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.additive_functor
import category_theory.abelian.basic
import category_theory.limits.preserves.shapes.kernels
import category_theory.adjunction.limits

/-!
# Transferring "abelian-ness" across a functor

If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>

## Notes
The hypotheses, following the statement from the Stacks project,
may appear suprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/

noncomputable theory

namespace category_theory
open category_theory.limits

universes v u₁ u₂

namespace abelian_of_adjunction

variables {C : Type u₁} [category.{v} C] [preadditive C]
variables {D : Type u₂} [category.{v} D] [abelian D]
variables (F : C ⥤ D)
variables (G : D ⥤ C) [functor.preserves_zero_morphisms G]
variables (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)

include i

/-- No point making this an instance, as it requires `i`. -/
lemma has_kernels [preserves_finite_limits G] : has_kernels C :=
{ has_limit := λ X Y f, begin
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_kernel (G.map (F.map f) ≫ i.hom.app _) := limits.has_kernel_comp_mono _ _,
    apply limits.has_kernel_iso_comp,
  end }

include adj

/-- No point making this an instance, as it requires `i` and `adj`. -/
lemma has_cokernels : has_cokernels C :=
{ has_colimit := λ X Y f, begin
    haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_cokernel (G.map (F.map f) ≫ i.hom.app _) := limits.has_cokernel_comp_iso _ _,
    apply limits.has_cokernel_epi_comp,
  end }

variables [limits.has_cokernels C]

/-- Auxiliary construction for `coimage_iso_image` -/
def cokernel_iso {X Y : C} (f : X ⟶ Y) : G.obj (cokernel (F.map f)) ≅ cokernel f :=
begin
  -- We have to write an explicit `preserves_colimits` type here,
  -- as `left_adjoint_preserves_colimits` has universe variables.
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
  calc G.obj (cokernel (F.map f))
      ≅ cokernel (G.map (F.map f)) : (as_iso (cokernel_comparison _ G)).symm
  ... ≅ cokernel (_ ≫ f ≫ _)       : cokernel_iso_of_eq (nat_iso.naturality_2 i f).symm
  ... ≅ cokernel (f ≫ _)           : cokernel_epi_comp _ _
  ... ≅ cokernel f                 : cokernel_comp_is_iso _ _
end

variables [limits.has_kernels C] [preserves_finite_limits G]

/-- Auxiliary construction for `coimage_iso_image` -/
def coimage_iso_image_aux {X Y : C} (f : X ⟶ Y) :
  kernel (G.map (cokernel.π (F.map f))) ≅ kernel (cokernel.π f) :=
begin
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
  calc kernel (G.map (cokernel.π (F.map f)))
      ≅ kernel (cokernel.π (G.map (F.map f)) ≫ cokernel_comparison (F.map f) G)
          : kernel_iso_of_eq (π_comp_cokernel_comparison _ _).symm
  ... ≅ kernel (cokernel.π (G.map (F.map f))) : kernel_comp_mono _ _
  ... ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernel_iso_of_eq _).hom)
          : kernel_iso_of_eq (π_comp_cokernel_iso_of_eq_hom (nat_iso.naturality_2 i f)).symm
  ... ≅ kernel (cokernel.π (_ ≫ f ≫ _))       : kernel_comp_mono _ _
  ... ≅ kernel (cokernel.π (f ≫ i.inv.app Y) ≫ (cokernel_epi_comp (i.hom.app X) _).inv)
          : kernel_iso_of_eq (by simp only [cokernel.π_desc, cokernel_epi_comp_inv])
  ... ≅ kernel (cokernel.π (f ≫ _))           : kernel_comp_mono _ _
  ... ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernel_comp_is_iso f (i.inv.app Y)).inv)
          : kernel_iso_of_eq (by simp only [cokernel.π_desc, cokernel_comp_is_iso_inv,
              iso.hom_inv_id_app_assoc, nat_iso.inv_inv_app])
  ... ≅ kernel (cokernel.π f ≫ _)             : kernel_is_iso_comp _ _
  ... ≅ kernel (cokernel.π f)                 : kernel_comp_mono _ _
end

variables [functor.preserves_zero_morphisms F]

/--
Auxiliary definition: the abelian coimage and abelian image agree.
We still need to check that this agrees with the canonical morphism.
-/
def coimage_iso_image {X Y : C} (f : X ⟶ Y) : abelian.coimage f ≅ abelian.image f :=
begin
  haveI : preserves_limits F := adj.right_adjoint_preserves_limits,
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits,
  calc abelian.coimage f
      ≅ cokernel (kernel.ι f)                 : iso.refl _
  ... ≅ G.obj (cokernel (F.map (kernel.ι f))) : (cokernel_iso _ _ i adj _).symm
  ... ≅ G.obj (cokernel (kernel_comparison f F ≫ (kernel.ι (F.map f))))
                                              : G.map_iso (cokernel_iso_of_eq (by simp))
  ... ≅ G.obj (cokernel (kernel.ι (F.map f))) : G.map_iso (cokernel_epi_comp _ _)
  ... ≅ G.obj (abelian.coimage (F.map f))     : iso.refl _
  ... ≅ G.obj (abelian.image (F.map f))       : G.map_iso (abelian.coimage_iso_image _)
  ... ≅ G.obj (kernel (cokernel.π (F.map f))) : iso.refl _
  ... ≅ kernel (G.map (cokernel.π (F.map f))) : preserves_kernel.iso _ _
  ... ≅ kernel (cokernel.π f)                 : coimage_iso_image_aux F G i adj f
  ... ≅ abelian.image f                       : iso.refl _,
end

local attribute [simp] cokernel_iso coimage_iso_image coimage_iso_image_aux

-- The account of this proof in the Stacks project omits this calculation.
-- Happily it's little effort: our `[ext]` and `[simp]` lemmas only need a little guidance.
lemma coimage_iso_image_hom {X Y : C} (f : X ⟶ Y) :
  (coimage_iso_image F G i adj f).hom = abelian.coimage_image_comparison f :=
by { ext, simpa [-functor.map_comp, ←G.map_comp_assoc] using nat_iso.naturality_1 i f, }

end abelian_of_adjunction

open abelian_of_adjunction

/--
If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>
-/
def abelian_of_adjunction
  {C : Type u₁} [category.{v} C] [preadditive C] [has_finite_products C]
  {D : Type u₂} [category.{v} D] [abelian D]
  (F : C ⥤ D) [functor.preserves_zero_morphisms F]
  (G : D ⥤ C) [functor.preserves_zero_morphisms G] [preserves_finite_limits G]
  (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F) : abelian C :=
begin
  haveI := has_kernels F G i, haveI := has_cokernels F G i adj,
  haveI : ∀ {X Y : C} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f),
  { intros X Y f, rw ←coimage_iso_image_hom F G i adj f, apply_instance, },
  apply abelian.of_coimage_image_comparison_is_iso,
end

/--
If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelian_of_equivalence
  {C : Type u₁} [category.{v} C] [preadditive C] [has_finite_products C]
  {D : Type u₂} [category.{v} D] [abelian D]
  (F : C ⥤ D) [functor.preserves_zero_morphisms F] [is_equivalence F] : abelian C :=
abelian_of_adjunction F F.inv F.as_equivalence.unit_iso.symm F.as_equivalence.symm.to_adjunction

end category_theory

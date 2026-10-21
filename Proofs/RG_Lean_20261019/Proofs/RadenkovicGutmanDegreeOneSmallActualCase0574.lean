/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0574 : Family 7 := level7.get ⟨28,by decide⟩
def sourceMap0574 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (sourceLabel 7 0 1 v)
def fusedMap0574 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0574_checked : acceptsGraphIso
    (source (graph core0574) (root 7) 0 1) DegreeOneSmallSpectrum264.graph sourceMap0574=true := by decide +kernel
theorem fusedMap0574_checked : acceptsGraphIso
    (fused (graph core0574) (root 7) 0 1) DegreeOneSmallSpectrum171.graph fusedMap0574=true := by decide +kernel
theorem certified0574 : Certified (graph core0574) (root 7) 0 1 :=
  of_native_maps core0574 DegreeOneSmallSpectrum264.graph DegreeOneSmallSpectrum171.graph
    sourceMap0574 fusedMap0574 sourceMap0574_checked fusedMap0574_checked
    DegreeOneSmallComparisons.comparison0574
#print axioms sourceMap0574_checked
#print axioms fusedMap0574_checked
#print axioms certified0574
def sourceMap0574swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 7 1 0 v)
def fusedMap0574swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0574swap_checked : acceptsGraphIso
    (source (graph core0574) (root 7) 1 0) DegreeOneSmallSpectrum264.graph sourceMap0574swap=true := by decide +kernel
theorem fusedMap0574swap_checked : acceptsGraphIso
    (fused (graph core0574) (root 7) 1 0) DegreeOneSmallSpectrum171.graph fusedMap0574swap=true := by decide +kernel
theorem certified0574swap : Certified (graph core0574) (root 7) 1 0 :=
  of_native_maps core0574 DegreeOneSmallSpectrum264.graph DegreeOneSmallSpectrum171.graph
    sourceMap0574swap fusedMap0574swap sourceMap0574swap_checked fusedMap0574swap_checked
    DegreeOneSmallComparisons.comparison0574
#print axioms sourceMap0574swap_checked
#print axioms fusedMap0574swap_checked
#print axioms certified0574swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

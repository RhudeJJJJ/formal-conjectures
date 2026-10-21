/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0172 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0172 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (sourceLabel 5 0 1 v)
def fusedMap0172 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap0172_checked : acceptsGraphIso
    (source (graph core0172) (root 5) 0 1) DegreeOneSmallSpectrum051.graph sourceMap0172=true := by decide +kernel
theorem fusedMap0172_checked : acceptsGraphIso
    (fused (graph core0172) (root 5) 0 1) DegreeOneSmallSpectrum034.graph fusedMap0172=true := by decide +kernel
theorem certified0172 : Certified (graph core0172) (root 5) 0 1 :=
  of_native_maps core0172 DegreeOneSmallSpectrum051.graph DegreeOneSmallSpectrum034.graph
    sourceMap0172 fusedMap0172 sourceMap0172_checked fusedMap0172_checked
    DegreeOneSmallComparisons.comparison0172
#print axioms sourceMap0172_checked
#print axioms fusedMap0172_checked
#print axioms certified0172
def sourceMap0172swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (sourceLabel 5 1 0 v)
def fusedMap0172swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap0172swap_checked : acceptsGraphIso
    (source (graph core0172) (root 5) 1 0) DegreeOneSmallSpectrum051.graph sourceMap0172swap=true := by decide +kernel
theorem fusedMap0172swap_checked : acceptsGraphIso
    (fused (graph core0172) (root 5) 1 0) DegreeOneSmallSpectrum034.graph fusedMap0172swap=true := by decide +kernel
theorem certified0172swap : Certified (graph core0172) (root 5) 1 0 :=
  of_native_maps core0172 DegreeOneSmallSpectrum051.graph DegreeOneSmallSpectrum034.graph
    sourceMap0172swap fusedMap0172swap sourceMap0172swap_checked fusedMap0172swap_checked
    DegreeOneSmallComparisons.comparison0172
#print axioms sourceMap0172swap_checked
#print axioms fusedMap0172swap_checked
#print axioms certified0172swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

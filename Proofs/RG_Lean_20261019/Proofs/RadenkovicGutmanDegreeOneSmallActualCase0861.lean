/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0861 : Family 8 := level8.get ⟨40,by decide⟩
def sourceMap0861 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0861 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0861_checked : acceptsGraphIso
    (source (graph core0861) (root 8) 0 2) DegreeOneSmallSpectrum1134.graph sourceMap0861=true := by decide +kernel
theorem fusedMap0861_checked : acceptsGraphIso
    (fused (graph core0861) (root 8) 0 2) DegreeOneSmallSpectrum872.graph fusedMap0861=true := by decide +kernel
theorem certified0861 : Certified (graph core0861) (root 8) 0 2 :=
  of_native_maps core0861 DegreeOneSmallSpectrum1134.graph DegreeOneSmallSpectrum872.graph
    sourceMap0861 fusedMap0861 sourceMap0861_checked fusedMap0861_checked
    DegreeOneSmallComparisons.comparison0861
#print axioms sourceMap0861_checked
#print axioms fusedMap0861_checked
#print axioms certified0861
def sourceMap0861swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0861swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0861swap_checked : acceptsGraphIso
    (source (graph core0861) (root 8) 2 0) DegreeOneSmallSpectrum1134.graph sourceMap0861swap=true := by decide +kernel
theorem fusedMap0861swap_checked : acceptsGraphIso
    (fused (graph core0861) (root 8) 2 0) DegreeOneSmallSpectrum872.graph fusedMap0861swap=true := by decide +kernel
theorem certified0861swap : Certified (graph core0861) (root 8) 2 0 :=
  of_native_maps core0861 DegreeOneSmallSpectrum1134.graph DegreeOneSmallSpectrum872.graph
    sourceMap0861swap fusedMap0861swap sourceMap0861swap_checked fusedMap0861swap_checked
    DegreeOneSmallComparisons.comparison0861
#print axioms sourceMap0861swap_checked
#print axioms fusedMap0861swap_checked
#print axioms certified0861swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

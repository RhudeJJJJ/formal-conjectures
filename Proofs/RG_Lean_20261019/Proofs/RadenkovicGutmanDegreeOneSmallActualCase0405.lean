/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0405 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0405 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap0405 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0405_checked : acceptsGraphIso
    (source (graph core0405) (root 6) 0 3) DegreeOneSmallSpectrum430.graph sourceMap0405=true := by decide +kernel
theorem fusedMap0405_checked : acceptsGraphIso
    (fused (graph core0405) (root 6) 0 3) DegreeOneSmallSpectrum434.graph fusedMap0405=true := by decide +kernel
theorem certified0405 : Certified (graph core0405) (root 6) 0 3 :=
  of_native_maps core0405 DegreeOneSmallSpectrum430.graph DegreeOneSmallSpectrum434.graph
    sourceMap0405 fusedMap0405 sourceMap0405_checked fusedMap0405_checked
    DegreeOneSmallComparisons.comparison0405
#print axioms sourceMap0405_checked
#print axioms fusedMap0405_checked
#print axioms certified0405
def sourceMap0405swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,7] (sourceLabel 6 3 0 v)
def fusedMap0405swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0405swap_checked : acceptsGraphIso
    (source (graph core0405) (root 6) 3 0) DegreeOneSmallSpectrum430.graph sourceMap0405swap=true := by decide +kernel
theorem fusedMap0405swap_checked : acceptsGraphIso
    (fused (graph core0405) (root 6) 3 0) DegreeOneSmallSpectrum434.graph fusedMap0405swap=true := by decide +kernel
theorem certified0405swap : Certified (graph core0405) (root 6) 3 0 :=
  of_native_maps core0405 DegreeOneSmallSpectrum430.graph DegreeOneSmallSpectrum434.graph
    sourceMap0405swap fusedMap0405swap sourceMap0405swap_checked fusedMap0405swap_checked
    DegreeOneSmallComparisons.comparison0405
#print axioms sourceMap0405swap_checked
#print axioms fusedMap0405swap_checked
#print axioms certified0405swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

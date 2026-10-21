/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0373 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0373 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0373 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0373_checked : acceptsGraphIso
    (source (graph core0373) (root 6) 1 3) DegreeOneSmallSpectrum1490.graph sourceMap0373=true := by decide +kernel
theorem fusedMap0373_checked : acceptsGraphIso
    (fused (graph core0373) (root 6) 1 3) DegreeOneSmallSpectrum951.graph fusedMap0373=true := by decide +kernel
theorem certified0373 : Certified (graph core0373) (root 6) 1 3 :=
  of_native_maps core0373 DegreeOneSmallSpectrum1490.graph DegreeOneSmallSpectrum951.graph
    sourceMap0373 fusedMap0373 sourceMap0373_checked fusedMap0373_checked
    DegreeOneSmallComparisons.comparison0373
#print axioms sourceMap0373_checked
#print axioms fusedMap0373_checked
#print axioms certified0373
def sourceMap0373swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0373swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0373swap_checked : acceptsGraphIso
    (source (graph core0373) (root 6) 3 1) DegreeOneSmallSpectrum1490.graph sourceMap0373swap=true := by decide +kernel
theorem fusedMap0373swap_checked : acceptsGraphIso
    (fused (graph core0373) (root 6) 3 1) DegreeOneSmallSpectrum951.graph fusedMap0373swap=true := by decide +kernel
theorem certified0373swap : Certified (graph core0373) (root 6) 3 1 :=
  of_native_maps core0373 DegreeOneSmallSpectrum1490.graph DegreeOneSmallSpectrum951.graph
    sourceMap0373swap fusedMap0373swap sourceMap0373swap_checked fusedMap0373swap_checked
    DegreeOneSmallComparisons.comparison0373
#print axioms sourceMap0373swap_checked
#print axioms fusedMap0373swap_checked
#print axioms certified0373swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

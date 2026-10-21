/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0397 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0397 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0397 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0397_checked : acceptsGraphIso
    (source (graph core0397) (root 6) 0 4) DegreeOneSmallSpectrum1027.graph sourceMap0397=true := by decide +kernel
theorem fusedMap0397_checked : acceptsGraphIso
    (fused (graph core0397) (root 6) 0 4) DegreeOneSmallSpectrum863.graph fusedMap0397=true := by decide +kernel
theorem certified0397 : Certified (graph core0397) (root 6) 0 4 :=
  of_native_maps core0397 DegreeOneSmallSpectrum1027.graph DegreeOneSmallSpectrum863.graph
    sourceMap0397 fusedMap0397 sourceMap0397_checked fusedMap0397_checked
    DegreeOneSmallComparisons.comparison0397
#print axioms sourceMap0397_checked
#print axioms fusedMap0397_checked
#print axioms certified0397
def sourceMap0397swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap0397swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0397swap_checked : acceptsGraphIso
    (source (graph core0397) (root 6) 4 0) DegreeOneSmallSpectrum1027.graph sourceMap0397swap=true := by decide +kernel
theorem fusedMap0397swap_checked : acceptsGraphIso
    (fused (graph core0397) (root 6) 4 0) DegreeOneSmallSpectrum863.graph fusedMap0397swap=true := by decide +kernel
theorem certified0397swap : Certified (graph core0397) (root 6) 4 0 :=
  of_native_maps core0397 DegreeOneSmallSpectrum1027.graph DegreeOneSmallSpectrum863.graph
    sourceMap0397swap fusedMap0397swap sourceMap0397swap_checked fusedMap0397swap_checked
    DegreeOneSmallComparisons.comparison0397
#print axioms sourceMap0397swap_checked
#print axioms fusedMap0397swap_checked
#print axioms certified0397swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

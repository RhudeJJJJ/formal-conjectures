/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0900 : Family 10 := level10.get ⟨1446,by decide⟩
def sourceMap0900 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0900 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0900_checked : acceptsGraphIso
    (source (graph core0900) (root 10) 0 0) DegreeOneSmallSpectrum1809.graph sourceMap0900=true := by decide +kernel
theorem fusedMap0900_checked : acceptsGraphIso
    (fused (graph core0900) (root 10) 0 0) DegreeOneSmallSpectrum1772.graph fusedMap0900=true := by decide +kernel
theorem certified0900 : Certified (graph core0900) (root 10) 0 0 :=
  of_native_maps core0900 DegreeOneSmallSpectrum1809.graph DegreeOneSmallSpectrum1772.graph
    sourceMap0900 fusedMap0900 sourceMap0900_checked fusedMap0900_checked
    DegreeTwoThreeFiniteComparisons.comparison0900
#print axioms sourceMap0900_checked
#print axioms fusedMap0900_checked
#print axioms certified0900
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

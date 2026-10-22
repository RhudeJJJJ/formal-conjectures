/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0620 : Family 10 := level10.get ⟨754,by decide⟩
def sourceMap0620 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0620 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0620_checked : acceptsGraphIso
    (source (graph core0620) (root 10) 0 0) DegreeTwoThreeSpectrum1390.graph sourceMap0620=true := by decide +kernel
theorem fusedMap0620_checked : acceptsGraphIso
    (fused (graph core0620) (root 10) 0 0) DegreeOneSmallSpectrum1381.graph fusedMap0620=true := by decide +kernel
theorem certified0620 : Certified (graph core0620) (root 10) 0 0 :=
  of_native_maps core0620 DegreeTwoThreeSpectrum1390.graph DegreeOneSmallSpectrum1381.graph
    sourceMap0620 fusedMap0620 sourceMap0620_checked fusedMap0620_checked
    DegreeTwoThreeFiniteComparisons.comparison0620
#print axioms sourceMap0620_checked
#print axioms fusedMap0620_checked
#print axioms certified0620
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

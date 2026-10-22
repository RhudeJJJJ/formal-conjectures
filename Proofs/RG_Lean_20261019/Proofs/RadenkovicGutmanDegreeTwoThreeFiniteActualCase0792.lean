/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0792 : Family 10 := level10.get ⟨1195,by decide⟩
def sourceMap0792 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0792 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0792_checked : acceptsGraphIso
    (source (graph core0792) (root 10) 0 0) DegreeOneSmallSpectrum1618.graph sourceMap0792=true := by decide +kernel
theorem fusedMap0792_checked : acceptsGraphIso
    (fused (graph core0792) (root 10) 0 0) DegreeOneSmallSpectrum1873.graph fusedMap0792=true := by decide +kernel
theorem certified0792 : Certified (graph core0792) (root 10) 0 0 :=
  of_native_maps core0792 DegreeOneSmallSpectrum1618.graph DegreeOneSmallSpectrum1873.graph
    sourceMap0792 fusedMap0792 sourceMap0792_checked fusedMap0792_checked
    DegreeTwoThreeFiniteComparisons.comparison0792
#print axioms sourceMap0792_checked
#print axioms fusedMap0792_checked
#print axioms certified0792
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

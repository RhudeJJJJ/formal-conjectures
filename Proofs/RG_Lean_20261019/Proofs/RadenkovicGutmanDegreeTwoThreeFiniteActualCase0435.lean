/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0435 : Family 10 := level10.get ⟨174,by decide⟩
def sourceMap0435 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,8,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0435 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0435_checked : acceptsGraphIso
    (source (graph core0435) (root 10) 0 0) DegreeOneSmallSpectrum1027.graph sourceMap0435=true := by decide +kernel
theorem fusedMap0435_checked : acceptsGraphIso
    (fused (graph core0435) (root 10) 0 0) DegreeOneSmallSpectrum925.graph fusedMap0435=true := by decide +kernel
theorem certified0435 : Certified (graph core0435) (root 10) 0 0 :=
  of_native_maps core0435 DegreeOneSmallSpectrum1027.graph DegreeOneSmallSpectrum925.graph
    sourceMap0435 fusedMap0435 sourceMap0435_checked fusedMap0435_checked
    DegreeTwoThreeFiniteComparisons.comparison0435
#print axioms sourceMap0435_checked
#print axioms fusedMap0435_checked
#print axioms certified0435
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

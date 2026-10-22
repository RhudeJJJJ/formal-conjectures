/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0557 : Family 10 := level10.get ⟨571,by decide⟩
def sourceMap0557 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0557 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0557_checked : acceptsGraphIso
    (source (graph core0557) (root 10) 0 0) DegreeOneSmallSpectrum1675.graph sourceMap0557=true := by decide +kernel
theorem fusedMap0557_checked : acceptsGraphIso
    (fused (graph core0557) (root 10) 0 0) DegreeOneSmallSpectrum1099.graph fusedMap0557=true := by decide +kernel
theorem certified0557 : Certified (graph core0557) (root 10) 0 0 :=
  of_native_maps core0557 DegreeOneSmallSpectrum1675.graph DegreeOneSmallSpectrum1099.graph
    sourceMap0557 fusedMap0557 sourceMap0557_checked fusedMap0557_checked
    DegreeTwoThreeFiniteComparisons.comparison0557
#print axioms sourceMap0557_checked
#print axioms fusedMap0557_checked
#print axioms certified0557
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

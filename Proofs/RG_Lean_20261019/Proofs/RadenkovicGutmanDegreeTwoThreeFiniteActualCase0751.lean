/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0751 : Family 10 := level10.get ⟨1087,by decide⟩
def sourceMap0751 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0751 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0751_checked : acceptsGraphIso
    (source (graph core0751) (root 10) 0 0) DegreeOneSmallSpectrum1071.graph sourceMap0751=true := by decide +kernel
theorem fusedMap0751_checked : acceptsGraphIso
    (fused (graph core0751) (root 10) 0 0) DegreeOneSmallSpectrum1070.graph fusedMap0751=true := by decide +kernel
theorem certified0751 : Certified (graph core0751) (root 10) 0 0 :=
  of_native_maps core0751 DegreeOneSmallSpectrum1071.graph DegreeOneSmallSpectrum1070.graph
    sourceMap0751 fusedMap0751 sourceMap0751_checked fusedMap0751_checked
    DegreeTwoThreeFiniteComparisons.comparison0751
#print axioms sourceMap0751_checked
#print axioms fusedMap0751_checked
#print axioms certified0751
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

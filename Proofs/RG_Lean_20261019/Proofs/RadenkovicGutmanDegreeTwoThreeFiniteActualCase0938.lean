/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0938 : Family 10 := level10.get ⟨1552,by decide⟩
def sourceMap0938 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0938 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0938_checked : acceptsGraphIso
    (source (graph core0938) (root 10) 0 0) DegreeTwoThreeSpectrum1325.graph sourceMap0938=true := by decide +kernel
theorem fusedMap0938_checked : acceptsGraphIso
    (fused (graph core0938) (root 10) 0 0) DegreeOneSmallSpectrum1575.graph fusedMap0938=true := by decide +kernel
theorem certified0938 : Certified (graph core0938) (root 10) 0 0 :=
  of_native_maps core0938 DegreeTwoThreeSpectrum1325.graph DegreeOneSmallSpectrum1575.graph
    sourceMap0938 fusedMap0938 sourceMap0938_checked fusedMap0938_checked
    DegreeTwoThreeFiniteComparisons.comparison0938
#print axioms sourceMap0938_checked
#print axioms fusedMap0938_checked
#print axioms certified0938
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

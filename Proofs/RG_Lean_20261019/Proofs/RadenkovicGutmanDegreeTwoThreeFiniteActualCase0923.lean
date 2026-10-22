/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0923 : Family 10 := level10.get ⟨1502,by decide⟩
def sourceMap0923 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0923 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0923_checked : acceptsGraphIso
    (source (graph core0923) (root 10) 0 0) DegreeOneSmallSpectrum1303.graph sourceMap0923=true := by decide +kernel
theorem fusedMap0923_checked : acceptsGraphIso
    (fused (graph core0923) (root 10) 0 0) DegreeOneSmallSpectrum1302.graph fusedMap0923=true := by decide +kernel
theorem certified0923 : Certified (graph core0923) (root 10) 0 0 :=
  of_native_maps core0923 DegreeOneSmallSpectrum1303.graph DegreeOneSmallSpectrum1302.graph
    sourceMap0923 fusedMap0923 sourceMap0923_checked fusedMap0923_checked
    DegreeTwoThreeFiniteComparisons.comparison0923
#print axioms sourceMap0923_checked
#print axioms fusedMap0923_checked
#print axioms certified0923
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

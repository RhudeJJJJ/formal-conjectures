/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0977 : Family 10 := level10.get ⟨1641,by decide⟩
def sourceMap0977 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0977 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0977_checked : acceptsGraphIso
    (source (graph core0977) (root 10) 0 0) DegreeOneSmallSpectrum1647.graph sourceMap0977=true := by decide +kernel
theorem fusedMap0977_checked : acceptsGraphIso
    (fused (graph core0977) (root 10) 0 0) DegreeOneSmallSpectrum1630.graph fusedMap0977=true := by decide +kernel
theorem certified0977 : Certified (graph core0977) (root 10) 0 0 :=
  of_native_maps core0977 DegreeOneSmallSpectrum1647.graph DegreeOneSmallSpectrum1630.graph
    sourceMap0977 fusedMap0977 sourceMap0977_checked fusedMap0977_checked
    DegreeTwoThreeFiniteComparisons.comparison0977
#print axioms sourceMap0977_checked
#print axioms fusedMap0977_checked
#print axioms certified0977
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

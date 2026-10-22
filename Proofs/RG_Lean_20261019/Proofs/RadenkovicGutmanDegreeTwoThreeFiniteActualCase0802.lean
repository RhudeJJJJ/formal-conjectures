/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0802 : Family 10 := level10.get ⟨1213,by decide⟩
def sourceMap0802 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0802 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0802_checked : acceptsGraphIso
    (source (graph core0802) (root 10) 0 0) DegreeOneSmallSpectrum1217.graph sourceMap0802=true := by decide +kernel
theorem fusedMap0802_checked : acceptsGraphIso
    (fused (graph core0802) (root 10) 0 0) DegreeOneSmallSpectrum1202.graph fusedMap0802=true := by decide +kernel
theorem certified0802 : Certified (graph core0802) (root 10) 0 0 :=
  of_native_maps core0802 DegreeOneSmallSpectrum1217.graph DegreeOneSmallSpectrum1202.graph
    sourceMap0802 fusedMap0802 sourceMap0802_checked fusedMap0802_checked
    DegreeTwoThreeFiniteComparisons.comparison0802
#print axioms sourceMap0802_checked
#print axioms fusedMap0802_checked
#print axioms certified0802
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

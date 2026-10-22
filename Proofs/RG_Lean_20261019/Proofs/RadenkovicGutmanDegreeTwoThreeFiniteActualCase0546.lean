/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0546 : Family 10 := level10.get ⟨538,by decide⟩
def sourceMap0546 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0546 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0546_checked : acceptsGraphIso
    (source (graph core0546) (root 10) 0 0) DegreeTwoThreeSpectrum1441.graph sourceMap0546=true := by decide +kernel
theorem fusedMap0546_checked : acceptsGraphIso
    (fused (graph core0546) (root 10) 0 0) DegreeOneSmallSpectrum1042.graph fusedMap0546=true := by decide +kernel
theorem certified0546 : Certified (graph core0546) (root 10) 0 0 :=
  of_native_maps core0546 DegreeTwoThreeSpectrum1441.graph DegreeOneSmallSpectrum1042.graph
    sourceMap0546 fusedMap0546 sourceMap0546_checked fusedMap0546_checked
    DegreeTwoThreeFiniteComparisons.comparison0546
#print axioms sourceMap0546_checked
#print axioms fusedMap0546_checked
#print axioms certified0546
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

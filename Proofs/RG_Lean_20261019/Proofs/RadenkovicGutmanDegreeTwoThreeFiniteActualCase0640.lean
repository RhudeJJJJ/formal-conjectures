/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0640 : Family 10 := level10.get ⟨810,by decide⟩
def sourceMap0640 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0640 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0640_checked : acceptsGraphIso
    (source (graph core0640) (root 10) 0 0) DegreeOneSmallSpectrum1628.graph sourceMap0640=true := by decide +kernel
theorem fusedMap0640_checked : acceptsGraphIso
    (fused (graph core0640) (root 10) 0 0) DegreeOneSmallSpectrum1406.graph fusedMap0640=true := by decide +kernel
theorem certified0640 : Certified (graph core0640) (root 10) 0 0 :=
  of_native_maps core0640 DegreeOneSmallSpectrum1628.graph DegreeOneSmallSpectrum1406.graph
    sourceMap0640 fusedMap0640 sourceMap0640_checked fusedMap0640_checked
    DegreeTwoThreeFiniteComparisons.comparison0640
#print axioms sourceMap0640_checked
#print axioms fusedMap0640_checked
#print axioms certified0640
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

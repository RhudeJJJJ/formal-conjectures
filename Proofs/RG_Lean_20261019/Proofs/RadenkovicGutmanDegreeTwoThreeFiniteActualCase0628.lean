/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0628 : Family 10 := level10.get ⟨777,by decide⟩
def sourceMap0628 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0628 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0628_checked : acceptsGraphIso
    (source (graph core0628) (root 10) 0 0) DegreeOneSmallSpectrum1664.graph sourceMap0628=true := by decide +kernel
theorem fusedMap0628_checked : acceptsGraphIso
    (fused (graph core0628) (root 10) 0 0) DegreeOneSmallSpectrum1409.graph fusedMap0628=true := by decide +kernel
theorem certified0628 : Certified (graph core0628) (root 10) 0 0 :=
  of_native_maps core0628 DegreeOneSmallSpectrum1664.graph DegreeOneSmallSpectrum1409.graph
    sourceMap0628 fusedMap0628 sourceMap0628_checked fusedMap0628_checked
    DegreeTwoThreeFiniteComparisons.comparison0628
#print axioms sourceMap0628_checked
#print axioms fusedMap0628_checked
#print axioms certified0628
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

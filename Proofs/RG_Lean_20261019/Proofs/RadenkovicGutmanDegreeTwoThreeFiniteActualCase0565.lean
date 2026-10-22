/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0565 : Family 10 := level10.get ⟨597,by decide⟩
def sourceMap0565 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0565 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0565_checked : acceptsGraphIso
    (source (graph core0565) (root 10) 0 0) DegreeOneSmallSpectrum1680.graph sourceMap0565=true := by decide +kernel
theorem fusedMap0565_checked : acceptsGraphIso
    (fused (graph core0565) (root 10) 0 0) DegreeOneSmallSpectrum1145.graph fusedMap0565=true := by decide +kernel
theorem certified0565 : Certified (graph core0565) (root 10) 0 0 :=
  of_native_maps core0565 DegreeOneSmallSpectrum1680.graph DegreeOneSmallSpectrum1145.graph
    sourceMap0565 fusedMap0565 sourceMap0565_checked fusedMap0565_checked
    DegreeTwoThreeFiniteComparisons.comparison0565
#print axioms sourceMap0565_checked
#print axioms fusedMap0565_checked
#print axioms certified0565
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

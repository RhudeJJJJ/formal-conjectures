/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0368 : Family 9 := level9.get ⟨597,by decide⟩
def sourceMap0368 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0368 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0368_checked : acceptsGraphIso
    (source (graph core0368) (root 9) 0 0) DegreeOneSmallSpectrum699.graph sourceMap0368=true := by decide +kernel
theorem fusedMap0368_checked : acceptsGraphIso
    (fused (graph core0368) (root 9) 0 0) DegreeOneSmallSpectrum698.graph fusedMap0368=true := by decide +kernel
theorem certified0368 : Certified (graph core0368) (root 9) 0 0 :=
  of_native_maps core0368 DegreeOneSmallSpectrum699.graph DegreeOneSmallSpectrum698.graph
    sourceMap0368 fusedMap0368 sourceMap0368_checked fusedMap0368_checked
    DegreeTwoThreeFiniteComparisons.comparison0368
#print axioms sourceMap0368_checked
#print axioms fusedMap0368_checked
#print axioms certified0368
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

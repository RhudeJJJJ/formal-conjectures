/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0336 : Family 9 := level9.get ⟨518,by decide⟩
def sourceMap0336 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0336 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0336_checked : acceptsGraphIso
    (source (graph core0336) (root 9) 0 0) DegreeOneSmallSpectrum468.graph sourceMap0336=true := by decide +kernel
theorem fusedMap0336_checked : acceptsGraphIso
    (fused (graph core0336) (root 9) 0 0) DegreeOneSmallSpectrum463.graph fusedMap0336=true := by decide +kernel
theorem certified0336 : Certified (graph core0336) (root 9) 0 0 :=
  of_native_maps core0336 DegreeOneSmallSpectrum468.graph DegreeOneSmallSpectrum463.graph
    sourceMap0336 fusedMap0336 sourceMap0336_checked fusedMap0336_checked
    DegreeTwoThreeFiniteComparisons.comparison0336
#print axioms sourceMap0336_checked
#print axioms fusedMap0336_checked
#print axioms certified0336
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

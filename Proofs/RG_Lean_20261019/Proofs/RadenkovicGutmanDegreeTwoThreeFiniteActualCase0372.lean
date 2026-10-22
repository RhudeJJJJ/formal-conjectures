/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0372 : Family 9 := level9.get ⟨605,by decide⟩
def sourceMap0372 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0372 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0372_checked : acceptsGraphIso
    (source (graph core0372) (root 9) 0 0) DegreeOneSmallSpectrum719.graph sourceMap0372=true := by decide +kernel
theorem fusedMap0372_checked : acceptsGraphIso
    (fused (graph core0372) (root 9) 0 0) DegreeOneSmallSpectrum699.graph fusedMap0372=true := by decide +kernel
theorem certified0372 : Certified (graph core0372) (root 9) 0 0 :=
  of_native_maps core0372 DegreeOneSmallSpectrum719.graph DegreeOneSmallSpectrum699.graph
    sourceMap0372 fusedMap0372 sourceMap0372_checked fusedMap0372_checked
    DegreeTwoThreeFiniteComparisons.comparison0372
#print axioms sourceMap0372_checked
#print axioms fusedMap0372_checked
#print axioms certified0372
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

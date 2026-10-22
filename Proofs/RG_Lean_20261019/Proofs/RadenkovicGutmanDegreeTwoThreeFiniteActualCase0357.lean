/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0357 : Family 9 := level9.get ⟨573,by decide⟩
def sourceMap0357 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0357 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0357_checked : acceptsGraphIso
    (source (graph core0357) (root 9) 0 0) DegreeOneSmallSpectrum657.graph sourceMap0357=true := by decide +kernel
theorem fusedMap0357_checked : acceptsGraphIso
    (fused (graph core0357) (root 9) 0 0) DegreeOneSmallSpectrum656.graph fusedMap0357=true := by decide +kernel
theorem certified0357 : Certified (graph core0357) (root 9) 0 0 :=
  of_native_maps core0357 DegreeOneSmallSpectrum657.graph DegreeOneSmallSpectrum656.graph
    sourceMap0357 fusedMap0357 sourceMap0357_checked fusedMap0357_checked
    DegreeTwoThreeFiniteComparisons.comparison0357
#print axioms sourceMap0357_checked
#print axioms fusedMap0357_checked
#print axioms certified0357
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

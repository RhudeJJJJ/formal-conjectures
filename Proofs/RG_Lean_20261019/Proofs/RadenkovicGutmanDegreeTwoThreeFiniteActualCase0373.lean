/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0373 : Family 9 := level9.get ⟨608,by decide⟩
def sourceMap0373 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0373 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0373_checked : acceptsGraphIso
    (source (graph core0373) (root 9) 0 0) DegreeOneSmallSpectrum731.graph sourceMap0373=true := by decide +kernel
theorem fusedMap0373_checked : acceptsGraphIso
    (fused (graph core0373) (root 9) 0 0) DegreeOneSmallSpectrum730.graph fusedMap0373=true := by decide +kernel
theorem certified0373 : Certified (graph core0373) (root 9) 0 0 :=
  of_native_maps core0373 DegreeOneSmallSpectrum731.graph DegreeOneSmallSpectrum730.graph
    sourceMap0373 fusedMap0373 sourceMap0373_checked fusedMap0373_checked
    DegreeTwoThreeFiniteComparisons.comparison0373
#print axioms sourceMap0373_checked
#print axioms fusedMap0373_checked
#print axioms certified0373
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

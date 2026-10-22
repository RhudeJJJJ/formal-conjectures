/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0295 : Family 9 := level9.get ⟨424,by decide⟩
def sourceMap0295 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0295 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0295_checked : acceptsGraphIso
    (source (graph core0295) (root 9) 0 0) DegreeTwoThreeSpectrum658.graph sourceMap0295=true := by decide +kernel
theorem fusedMap0295_checked : acceptsGraphIso
    (fused (graph core0295) (root 9) 0 0) DegreeOneSmallSpectrum784.graph fusedMap0295=true := by decide +kernel
theorem certified0295 : Certified (graph core0295) (root 9) 0 0 :=
  of_native_maps core0295 DegreeTwoThreeSpectrum658.graph DegreeOneSmallSpectrum784.graph
    sourceMap0295 fusedMap0295 sourceMap0295_checked fusedMap0295_checked
    DegreeTwoThreeFiniteComparisons.comparison0295
#print axioms sourceMap0295_checked
#print axioms fusedMap0295_checked
#print axioms certified0295
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0281 : Family 9 := level9.get ⟨392,by decide⟩
def sourceMap0281 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0281 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,8,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0281_checked : acceptsGraphIso
    (source (graph core0281) (root 9) 0 0) DegreeOneSmallSpectrum628.graph sourceMap0281=true := by decide +kernel
theorem fusedMap0281_checked : acceptsGraphIso
    (fused (graph core0281) (root 9) 0 0) DegreeOneSmallSpectrum762.graph fusedMap0281=true := by decide +kernel
theorem certified0281 : Certified (graph core0281) (root 9) 0 0 :=
  of_native_maps core0281 DegreeOneSmallSpectrum628.graph DegreeOneSmallSpectrum762.graph
    sourceMap0281 fusedMap0281 sourceMap0281_checked fusedMap0281_checked
    DegreeTwoThreeFiniteComparisons.comparison0281
#print axioms sourceMap0281_checked
#print axioms fusedMap0281_checked
#print axioms certified0281
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

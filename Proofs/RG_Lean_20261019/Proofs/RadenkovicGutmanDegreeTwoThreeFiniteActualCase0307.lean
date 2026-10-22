/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0307 : Family 9 := level9.get ⟨454,by decide⟩
def sourceMap0307 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0307 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0307_checked : acceptsGraphIso
    (source (graph core0307) (root 9) 0 0) DegreeOneSmallSpectrum532.graph sourceMap0307=true := by decide +kernel
theorem fusedMap0307_checked : acceptsGraphIso
    (fused (graph core0307) (root 9) 0 0) DegreeOneSmallSpectrum531.graph fusedMap0307=true := by decide +kernel
theorem certified0307 : Certified (graph core0307) (root 9) 0 0 :=
  of_native_maps core0307 DegreeOneSmallSpectrum532.graph DegreeOneSmallSpectrum531.graph
    sourceMap0307 fusedMap0307 sourceMap0307_checked fusedMap0307_checked
    DegreeTwoThreeFiniteComparisons.comparison0307
#print axioms sourceMap0307_checked
#print axioms fusedMap0307_checked
#print axioms certified0307
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

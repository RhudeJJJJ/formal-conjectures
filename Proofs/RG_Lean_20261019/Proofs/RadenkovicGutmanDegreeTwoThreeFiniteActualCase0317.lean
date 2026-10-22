/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0317 : Family 9 := level9.get ⟨477,by decide⟩
def sourceMap0317 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0317 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0317_checked : acceptsGraphIso
    (source (graph core0317) (root 9) 0 0) DegreeOneSmallSpectrum560.graph sourceMap0317=true := by decide +kernel
theorem fusedMap0317_checked : acceptsGraphIso
    (fused (graph core0317) (root 9) 0 0) DegreeOneSmallSpectrum559.graph fusedMap0317=true := by decide +kernel
theorem certified0317 : Certified (graph core0317) (root 9) 0 0 :=
  of_native_maps core0317 DegreeOneSmallSpectrum560.graph DegreeOneSmallSpectrum559.graph
    sourceMap0317 fusedMap0317 sourceMap0317_checked fusedMap0317_checked
    DegreeTwoThreeFiniteComparisons.comparison0317
#print axioms sourceMap0317_checked
#print axioms fusedMap0317_checked
#print axioms certified0317
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

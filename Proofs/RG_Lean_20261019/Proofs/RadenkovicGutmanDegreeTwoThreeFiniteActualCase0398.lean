/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0398 : Family 9 := level9.get ⟨696,by decide⟩
def sourceMap0398 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0398 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0398_checked : acceptsGraphIso
    (source (graph core0398) (root 9) 0 0) DegreeTwoThreeSpectrum711.graph sourceMap0398=true := by decide +kernel
theorem fusedMap0398_checked : acceptsGraphIso
    (fused (graph core0398) (root 9) 0 0) DegreeTwoThreeSpectrum710.graph fusedMap0398=true := by decide +kernel
theorem certified0398 : Certified (graph core0398) (root 9) 0 0 :=
  of_native_maps core0398 DegreeTwoThreeSpectrum711.graph DegreeTwoThreeSpectrum710.graph
    sourceMap0398 fusedMap0398 sourceMap0398_checked fusedMap0398_checked
    DegreeTwoThreeFiniteComparisons.comparison0398
#print axioms sourceMap0398_checked
#print axioms fusedMap0398_checked
#print axioms certified0398
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

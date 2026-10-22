/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0392 : Family 9 := level9.get ⟨659,by decide⟩
def sourceMap0392 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0392 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0392_checked : acceptsGraphIso
    (source (graph core0392) (root 9) 0 0) DegreeTwoThreeSpectrum559.graph sourceMap0392=true := by decide +kernel
theorem fusedMap0392_checked : acceptsGraphIso
    (fused (graph core0392) (root 9) 0 0) DegreeTwoThreeSpectrum548.graph fusedMap0392=true := by decide +kernel
theorem certified0392 : Certified (graph core0392) (root 9) 0 0 :=
  of_native_maps core0392 DegreeTwoThreeSpectrum559.graph DegreeTwoThreeSpectrum548.graph
    sourceMap0392 fusedMap0392 sourceMap0392_checked fusedMap0392_checked
    DegreeTwoThreeFiniteComparisons.comparison0392
#print axioms sourceMap0392_checked
#print axioms fusedMap0392_checked
#print axioms certified0392
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

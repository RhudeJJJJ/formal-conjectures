/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3140 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap3140 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,8,1,2,3,4,5,6] (sourceLabel 8 0 5 v)
def fusedMap3140 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (fusedLabel 8 0 5 v)
theorem sourceMap3140_checked : acceptsGraphIso
    (source (graph core3140) (root 8) 0 5) DegreeTwoThreeSpectrum3889.graph sourceMap3140=true := by decide +kernel
theorem fusedMap3140_checked : acceptsGraphIso
    (fused (graph core3140) (root 8) 0 5) DegreeTwoThreeSpectrum3892.graph fusedMap3140=true := by decide +kernel
theorem certified3140 : Certified (graph core3140) (root 8) 0 5 :=
  of_native_maps core3140 DegreeTwoThreeSpectrum3889.graph DegreeTwoThreeSpectrum3892.graph
    sourceMap3140 fusedMap3140 sourceMap3140_checked fusedMap3140_checked
    DegreeTwoThreeFiniteComparisons.comparison3140
#print axioms sourceMap3140_checked
#print axioms fusedMap3140_checked
#print axioms certified3140
def sourceMap3140swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,1,2,3,4,5,6,8] (sourceLabel 8 5 0 v)
def fusedMap3140swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (fusedLabel 8 5 0 v)
theorem sourceMap3140swap_checked : acceptsGraphIso
    (source (graph core3140) (root 8) 5 0) DegreeTwoThreeSpectrum3889.graph sourceMap3140swap=true := by decide +kernel
theorem fusedMap3140swap_checked : acceptsGraphIso
    (fused (graph core3140) (root 8) 5 0) DegreeTwoThreeSpectrum3892.graph fusedMap3140swap=true := by decide +kernel
theorem certified3140swap : Certified (graph core3140) (root 8) 5 0 :=
  of_native_maps core3140 DegreeTwoThreeSpectrum3889.graph DegreeTwoThreeSpectrum3892.graph
    sourceMap3140swap fusedMap3140swap sourceMap3140swap_checked fusedMap3140swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3140
#print axioms sourceMap3140swap_checked
#print axioms fusedMap3140swap_checked
#print axioms certified3140swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

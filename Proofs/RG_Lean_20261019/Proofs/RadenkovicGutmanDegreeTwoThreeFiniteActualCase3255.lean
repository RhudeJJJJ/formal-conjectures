/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3255 : Family 9 := level9.get ⟨91,by decide⟩
def sourceMap3255 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 9 0 5 v)
def fusedMap3255 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3255_checked : acceptsGraphIso
    (source (graph core3255) (root 9) 0 5) DegreeTwoThreeSpectrum5654.graph sourceMap3255=true := by decide +kernel
theorem fusedMap3255_checked : acceptsGraphIso
    (fused (graph core3255) (root 9) 0 5) DegreeTwoThreeSpectrum5039.graph fusedMap3255=true := by decide +kernel
theorem certified3255 : Certified (graph core3255) (root 9) 0 5 :=
  of_native_maps core3255 DegreeTwoThreeSpectrum5654.graph DegreeTwoThreeSpectrum5039.graph
    sourceMap3255 fusedMap3255 sourceMap3255_checked fusedMap3255_checked
    DegreeTwoThreeFiniteComparisons.comparison3255
#print axioms sourceMap3255_checked
#print axioms fusedMap3255_checked
#print axioms certified3255
def sourceMap3255swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13,16] (sourceLabel 9 5 0 v)
def fusedMap3255swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3255swap_checked : acceptsGraphIso
    (source (graph core3255) (root 9) 5 0) DegreeTwoThreeSpectrum5654.graph sourceMap3255swap=true := by decide +kernel
theorem fusedMap3255swap_checked : acceptsGraphIso
    (fused (graph core3255) (root 9) 5 0) DegreeTwoThreeSpectrum5039.graph fusedMap3255swap=true := by decide +kernel
theorem certified3255swap : Certified (graph core3255) (root 9) 5 0 :=
  of_native_maps core3255 DegreeTwoThreeSpectrum5654.graph DegreeTwoThreeSpectrum5039.graph
    sourceMap3255swap fusedMap3255swap sourceMap3255swap_checked fusedMap3255swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3255
#print axioms sourceMap3255swap_checked
#print axioms fusedMap3255swap_checked
#print axioms certified3255swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

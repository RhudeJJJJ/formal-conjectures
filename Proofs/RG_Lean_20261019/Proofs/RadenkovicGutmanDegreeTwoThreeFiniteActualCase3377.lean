/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3377 : Family 9 := level9.get ⟨440,by decide⟩
def sourceMap3377 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3377 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3377_checked : acceptsGraphIso
    (source (graph core3377) (root 9) 0 5) DegreeTwoThreeSpectrum6595.graph sourceMap3377=true := by decide +kernel
theorem fusedMap3377_checked : acceptsGraphIso
    (fused (graph core3377) (root 9) 0 5) DegreeTwoThreeSpectrum5483.graph fusedMap3377=true := by decide +kernel
theorem certified3377 : Certified (graph core3377) (root 9) 0 5 :=
  of_native_maps core3377 DegreeTwoThreeSpectrum6595.graph DegreeTwoThreeSpectrum5483.graph
    sourceMap3377 fusedMap3377 sourceMap3377_checked fusedMap3377_checked
    DegreeTwoThreeFiniteComparisons.comparison3377
#print axioms sourceMap3377_checked
#print axioms fusedMap3377_checked
#print axioms certified3377
def sourceMap3377swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3377swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3377swap_checked : acceptsGraphIso
    (source (graph core3377) (root 9) 5 0) DegreeTwoThreeSpectrum6595.graph sourceMap3377swap=true := by decide +kernel
theorem fusedMap3377swap_checked : acceptsGraphIso
    (fused (graph core3377) (root 9) 5 0) DegreeTwoThreeSpectrum5483.graph fusedMap3377swap=true := by decide +kernel
theorem certified3377swap : Certified (graph core3377) (root 9) 5 0 :=
  of_native_maps core3377 DegreeTwoThreeSpectrum6595.graph DegreeTwoThreeSpectrum5483.graph
    sourceMap3377swap fusedMap3377swap sourceMap3377swap_checked fusedMap3377swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3377
#print axioms sourceMap3377swap_checked
#print axioms fusedMap3377swap_checked
#print axioms certified3377swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

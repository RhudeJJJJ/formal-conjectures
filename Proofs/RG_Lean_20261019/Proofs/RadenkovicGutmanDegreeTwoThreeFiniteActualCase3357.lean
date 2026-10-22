/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3357 : Family 9 := level9.get ⟨392,by decide⟩
def sourceMap3357 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3357 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3357_checked : acceptsGraphIso
    (source (graph core3357) (root 9) 0 5) DegreeTwoThreeSpectrum6366.graph sourceMap3357=true := by decide +kernel
theorem fusedMap3357_checked : acceptsGraphIso
    (fused (graph core3357) (root 9) 0 5) DegreeTwoThreeSpectrum5313.graph fusedMap3357=true := by decide +kernel
theorem certified3357 : Certified (graph core3357) (root 9) 0 5 :=
  of_native_maps core3357 DegreeTwoThreeSpectrum6366.graph DegreeTwoThreeSpectrum5313.graph
    sourceMap3357 fusedMap3357 sourceMap3357_checked fusedMap3357_checked
    DegreeTwoThreeFiniteComparisons.comparison3357
#print axioms sourceMap3357_checked
#print axioms fusedMap3357_checked
#print axioms certified3357
def sourceMap3357swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3357swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3357swap_checked : acceptsGraphIso
    (source (graph core3357) (root 9) 5 0) DegreeTwoThreeSpectrum6366.graph sourceMap3357swap=true := by decide +kernel
theorem fusedMap3357swap_checked : acceptsGraphIso
    (fused (graph core3357) (root 9) 5 0) DegreeTwoThreeSpectrum5313.graph fusedMap3357swap=true := by decide +kernel
theorem certified3357swap : Certified (graph core3357) (root 9) 5 0 :=
  of_native_maps core3357 DegreeTwoThreeSpectrum6366.graph DegreeTwoThreeSpectrum5313.graph
    sourceMap3357swap fusedMap3357swap sourceMap3357swap_checked fusedMap3357swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3357
#print axioms sourceMap3357swap_checked
#print axioms fusedMap3357swap_checked
#print axioms certified3357swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

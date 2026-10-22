/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3363 : Family 9 := level9.get ⟨403,by decide⟩
def sourceMap3363 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3363 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3363_checked : acceptsGraphIso
    (source (graph core3363) (root 9) 0 5) DegreeTwoThreeSpectrum6408.graph sourceMap3363=true := by decide +kernel
theorem fusedMap3363_checked : acceptsGraphIso
    (fused (graph core3363) (root 9) 0 5) DegreeTwoThreeSpectrum5340.graph fusedMap3363=true := by decide +kernel
theorem certified3363 : Certified (graph core3363) (root 9) 0 5 :=
  of_native_maps core3363 DegreeTwoThreeSpectrum6408.graph DegreeTwoThreeSpectrum5340.graph
    sourceMap3363 fusedMap3363 sourceMap3363_checked fusedMap3363_checked
    DegreeTwoThreeFiniteComparisons.comparison3363
#print axioms sourceMap3363_checked
#print axioms fusedMap3363_checked
#print axioms certified3363
def sourceMap3363swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3363swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3363swap_checked : acceptsGraphIso
    (source (graph core3363) (root 9) 5 0) DegreeTwoThreeSpectrum6408.graph sourceMap3363swap=true := by decide +kernel
theorem fusedMap3363swap_checked : acceptsGraphIso
    (fused (graph core3363) (root 9) 5 0) DegreeTwoThreeSpectrum5340.graph fusedMap3363swap=true := by decide +kernel
theorem certified3363swap : Certified (graph core3363) (root 9) 5 0 :=
  of_native_maps core3363 DegreeTwoThreeSpectrum6408.graph DegreeTwoThreeSpectrum5340.graph
    sourceMap3363swap fusedMap3363swap sourceMap3363swap_checked fusedMap3363swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3363
#print axioms sourceMap3363swap_checked
#print axioms fusedMap3363swap_checked
#print axioms certified3363swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

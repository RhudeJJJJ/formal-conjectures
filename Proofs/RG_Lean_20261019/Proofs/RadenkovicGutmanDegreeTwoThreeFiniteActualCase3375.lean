/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3375 : Family 9 := level9.get ⟨434,by decide⟩
def sourceMap3375 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3375 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3375_checked : acceptsGraphIso
    (source (graph core3375) (root 9) 0 5) DegreeTwoThreeSpectrum6567.graph sourceMap3375=true := by decide +kernel
theorem fusedMap3375_checked : acceptsGraphIso
    (fused (graph core3375) (root 9) 0 5) DegreeTwoThreeSpectrum5459.graph fusedMap3375=true := by decide +kernel
theorem certified3375 : Certified (graph core3375) (root 9) 0 5 :=
  of_native_maps core3375 DegreeTwoThreeSpectrum6567.graph DegreeTwoThreeSpectrum5459.graph
    sourceMap3375 fusedMap3375 sourceMap3375_checked fusedMap3375_checked
    DegreeTwoThreeFiniteComparisons.comparison3375
#print axioms sourceMap3375_checked
#print axioms fusedMap3375_checked
#print axioms certified3375
def sourceMap3375swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3375swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3375swap_checked : acceptsGraphIso
    (source (graph core3375) (root 9) 5 0) DegreeTwoThreeSpectrum6567.graph sourceMap3375swap=true := by decide +kernel
theorem fusedMap3375swap_checked : acceptsGraphIso
    (fused (graph core3375) (root 9) 5 0) DegreeTwoThreeSpectrum5459.graph fusedMap3375swap=true := by decide +kernel
theorem certified3375swap : Certified (graph core3375) (root 9) 5 0 :=
  of_native_maps core3375 DegreeTwoThreeSpectrum6567.graph DegreeTwoThreeSpectrum5459.graph
    sourceMap3375swap fusedMap3375swap sourceMap3375swap_checked fusedMap3375swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3375
#print axioms sourceMap3375swap_checked
#print axioms fusedMap3375swap_checked
#print axioms certified3375swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

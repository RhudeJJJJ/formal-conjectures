/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3368 : Family 9 := level9.get ⟨417,by decide⟩
def sourceMap3368 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3368 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3368_checked : acceptsGraphIso
    (source (graph core3368) (root 9) 0 5) DegreeTwoThreeSpectrum6484.graph sourceMap3368=true := by decide +kernel
theorem fusedMap3368_checked : acceptsGraphIso
    (fused (graph core3368) (root 9) 0 5) DegreeTwoThreeSpectrum5422.graph fusedMap3368=true := by decide +kernel
theorem certified3368 : Certified (graph core3368) (root 9) 0 5 :=
  of_native_maps core3368 DegreeTwoThreeSpectrum6484.graph DegreeTwoThreeSpectrum5422.graph
    sourceMap3368 fusedMap3368 sourceMap3368_checked fusedMap3368_checked
    DegreeTwoThreeFiniteComparisons.comparison3368
#print axioms sourceMap3368_checked
#print axioms fusedMap3368_checked
#print axioms certified3368
def sourceMap3368swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3368swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3368swap_checked : acceptsGraphIso
    (source (graph core3368) (root 9) 5 0) DegreeTwoThreeSpectrum6484.graph sourceMap3368swap=true := by decide +kernel
theorem fusedMap3368swap_checked : acceptsGraphIso
    (fused (graph core3368) (root 9) 5 0) DegreeTwoThreeSpectrum5422.graph fusedMap3368swap=true := by decide +kernel
theorem certified3368swap : Certified (graph core3368) (root 9) 5 0 :=
  of_native_maps core3368 DegreeTwoThreeSpectrum6484.graph DegreeTwoThreeSpectrum5422.graph
    sourceMap3368swap fusedMap3368swap sourceMap3368swap_checked fusedMap3368swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3368
#print axioms sourceMap3368swap_checked
#print axioms fusedMap3368swap_checked
#print axioms certified3368swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3320 : Family 9 := level9.get ⟨294,by decide⟩
def sourceMap3320 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3320 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3320_checked : acceptsGraphIso
    (source (graph core3320) (root 9) 0 5) DegreeTwoThreeSpectrum5846.graph sourceMap3320=true := by decide +kernel
theorem fusedMap3320_checked : acceptsGraphIso
    (fused (graph core3320) (root 9) 0 5) DegreeTwoThreeSpectrum5847.graph fusedMap3320=true := by decide +kernel
theorem certified3320 : Certified (graph core3320) (root 9) 0 5 :=
  of_native_maps core3320 DegreeTwoThreeSpectrum5846.graph DegreeTwoThreeSpectrum5847.graph
    sourceMap3320 fusedMap3320 sourceMap3320_checked fusedMap3320_checked
    DegreeTwoThreeFiniteComparisons.comparison3320
#print axioms sourceMap3320_checked
#print axioms fusedMap3320_checked
#print axioms certified3320
def sourceMap3320swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3320swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3320swap_checked : acceptsGraphIso
    (source (graph core3320) (root 9) 5 0) DegreeTwoThreeSpectrum5846.graph sourceMap3320swap=true := by decide +kernel
theorem fusedMap3320swap_checked : acceptsGraphIso
    (fused (graph core3320) (root 9) 5 0) DegreeTwoThreeSpectrum5847.graph fusedMap3320swap=true := by decide +kernel
theorem certified3320swap : Certified (graph core3320) (root 9) 5 0 :=
  of_native_maps core3320 DegreeTwoThreeSpectrum5846.graph DegreeTwoThreeSpectrum5847.graph
    sourceMap3320swap fusedMap3320swap sourceMap3320swap_checked fusedMap3320swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3320
#print axioms sourceMap3320swap_checked
#print axioms fusedMap3320swap_checked
#print axioms certified3320swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

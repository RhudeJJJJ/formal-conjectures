/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3553 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap3553 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3553 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3553_checked : acceptsGraphIso
    (source (graph core3553) (root 8) 0 6) DegreeTwoThreeSpectrum5589.graph sourceMap3553=true := by decide +kernel
theorem fusedMap3553_checked : acceptsGraphIso
    (fused (graph core3553) (root 8) 0 6) DegreeTwoThreeSpectrum5024.graph fusedMap3553=true := by decide +kernel
theorem certified3553 : Certified (graph core3553) (root 8) 0 6 :=
  of_native_maps core3553 DegreeTwoThreeSpectrum5589.graph DegreeTwoThreeSpectrum5024.graph
    sourceMap3553 fusedMap3553 sourceMap3553_checked fusedMap3553_checked
    DegreeTwoThreeFiniteComparisons.comparison3553
#print axioms sourceMap3553_checked
#print axioms fusedMap3553_checked
#print axioms certified3553
def sourceMap3553swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3553swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3553swap_checked : acceptsGraphIso
    (source (graph core3553) (root 8) 6 0) DegreeTwoThreeSpectrum5589.graph sourceMap3553swap=true := by decide +kernel
theorem fusedMap3553swap_checked : acceptsGraphIso
    (fused (graph core3553) (root 8) 6 0) DegreeTwoThreeSpectrum5024.graph fusedMap3553swap=true := by decide +kernel
theorem certified3553swap : Certified (graph core3553) (root 8) 6 0 :=
  of_native_maps core3553 DegreeTwoThreeSpectrum5589.graph DegreeTwoThreeSpectrum5024.graph
    sourceMap3553swap fusedMap3553swap sourceMap3553swap_checked fusedMap3553swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3553
#print axioms sourceMap3553swap_checked
#print axioms fusedMap3553swap_checked
#print axioms certified3553swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

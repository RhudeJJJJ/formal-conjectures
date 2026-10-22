/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3160 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap3160 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3160 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3160_checked : acceptsGraphIso
    (source (graph core3160) (root 8) 0 5) DegreeTwoThreeSpectrum4106.graph sourceMap3160=true := by decide +kernel
theorem fusedMap3160_checked : acceptsGraphIso
    (fused (graph core3160) (root 8) 0 5) DegreeTwoThreeSpectrum4107.graph fusedMap3160=true := by decide +kernel
theorem certified3160 : Certified (graph core3160) (root 8) 0 5 :=
  of_native_maps core3160 DegreeTwoThreeSpectrum4106.graph DegreeTwoThreeSpectrum4107.graph
    sourceMap3160 fusedMap3160 sourceMap3160_checked fusedMap3160_checked
    DegreeTwoThreeFiniteComparisons.comparison3160
#print axioms sourceMap3160_checked
#print axioms fusedMap3160_checked
#print axioms certified3160
def sourceMap3160swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3160swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3160swap_checked : acceptsGraphIso
    (source (graph core3160) (root 8) 5 0) DegreeTwoThreeSpectrum4106.graph sourceMap3160swap=true := by decide +kernel
theorem fusedMap3160swap_checked : acceptsGraphIso
    (fused (graph core3160) (root 8) 5 0) DegreeTwoThreeSpectrum4107.graph fusedMap3160swap=true := by decide +kernel
theorem certified3160swap : Certified (graph core3160) (root 8) 5 0 :=
  of_native_maps core3160 DegreeTwoThreeSpectrum4106.graph DegreeTwoThreeSpectrum4107.graph
    sourceMap3160swap fusedMap3160swap sourceMap3160swap_checked fusedMap3160swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3160
#print axioms sourceMap3160swap_checked
#print axioms fusedMap3160swap_checked
#print axioms certified3160swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3187 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap3187 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3187 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3187_checked : acceptsGraphIso
    (source (graph core3187) (root 8) 0 5) DegreeTwoThreeSpectrum4512.graph sourceMap3187=true := by decide +kernel
theorem fusedMap3187_checked : acceptsGraphIso
    (fused (graph core3187) (root 8) 0 5) DegreeTwoThreeSpectrum4027.graph fusedMap3187=true := by decide +kernel
theorem certified3187 : Certified (graph core3187) (root 8) 0 5 :=
  of_native_maps core3187 DegreeTwoThreeSpectrum4512.graph DegreeTwoThreeSpectrum4027.graph
    sourceMap3187 fusedMap3187 sourceMap3187_checked fusedMap3187_checked
    DegreeTwoThreeFiniteComparisons.comparison3187
#print axioms sourceMap3187_checked
#print axioms fusedMap3187_checked
#print axioms certified3187
def sourceMap3187swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3187swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3187swap_checked : acceptsGraphIso
    (source (graph core3187) (root 8) 5 0) DegreeTwoThreeSpectrum4512.graph sourceMap3187swap=true := by decide +kernel
theorem fusedMap3187swap_checked : acceptsGraphIso
    (fused (graph core3187) (root 8) 5 0) DegreeTwoThreeSpectrum4027.graph fusedMap3187swap=true := by decide +kernel
theorem certified3187swap : Certified (graph core3187) (root 8) 5 0 :=
  of_native_maps core3187 DegreeTwoThreeSpectrum4512.graph DegreeTwoThreeSpectrum4027.graph
    sourceMap3187swap fusedMap3187swap sourceMap3187swap_checked fusedMap3187swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3187
#print axioms sourceMap3187swap_checked
#print axioms fusedMap3187swap_checked
#print axioms certified3187swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

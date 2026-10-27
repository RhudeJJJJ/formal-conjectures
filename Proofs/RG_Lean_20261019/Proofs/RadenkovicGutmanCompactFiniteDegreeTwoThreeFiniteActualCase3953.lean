/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3953 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap3953 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3953 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3953_checked : acceptsGraphIso
    (source (graph core3953) (root 7) 1 5) DegreeTwoThreeSpectrum4106.graph sourceMap3953=true := by decide +kernel
theorem fusedMap3953_checked : acceptsGraphIso
    (fused (graph core3953) (root 7) 1 5) DegreeTwoThreeSpectrum3873.graph fusedMap3953=true := by decide +kernel
theorem certified3953 : Certified (graph core3953) (root 7) 1 5 :=
  of_native_maps core3953 DegreeTwoThreeSpectrum4106.graph DegreeTwoThreeSpectrum3873.graph
    sourceMap3953 fusedMap3953 sourceMap3953_checked fusedMap3953_checked
    DegreeTwoThreeFiniteComparisons.comparison3953
#print axioms sourceMap3953_checked
#print axioms fusedMap3953_checked
#print axioms certified3953
def sourceMap3953swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,15,7,8] (sourceLabel 7 5 1 v)
def fusedMap3953swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3953swap_checked : acceptsGraphIso
    (source (graph core3953) (root 7) 5 1) DegreeTwoThreeSpectrum4106.graph sourceMap3953swap=true := by decide +kernel
theorem fusedMap3953swap_checked : acceptsGraphIso
    (fused (graph core3953) (root 7) 5 1) DegreeTwoThreeSpectrum3873.graph fusedMap3953swap=true := by decide +kernel
theorem certified3953swap : Certified (graph core3953) (root 7) 5 1 :=
  of_native_maps core3953 DegreeTwoThreeSpectrum4106.graph DegreeTwoThreeSpectrum3873.graph
    sourceMap3953swap fusedMap3953swap sourceMap3953swap_checked fusedMap3953swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3953
#print axioms sourceMap3953swap_checked
#print axioms fusedMap3953swap_checked
#print axioms certified3953swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

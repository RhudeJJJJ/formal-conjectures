/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3793 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap3793 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,12,13,7,8,9,10,11] (sourceLabel 7 1 4 v)
def fusedMap3793 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3793_checked : acceptsGraphIso
    (source (graph core3793) (root 7) 1 4) DegreeTwoThreeSpectrum2940.graph sourceMap3793=true := by decide +kernel
theorem fusedMap3793_checked : acceptsGraphIso
    (fused (graph core3793) (root 7) 1 4) DegreeTwoThreeSpectrum2402.graph fusedMap3793=true := by decide +kernel
theorem certified3793 : Certified (graph core3793) (root 7) 1 4 :=
  of_native_maps core3793 DegreeTwoThreeSpectrum2940.graph DegreeTwoThreeSpectrum2402.graph
    sourceMap3793 fusedMap3793 sourceMap3793_checked fusedMap3793_checked
    DegreeTwoThreeFiniteComparisons.comparison3793
#print axioms sourceMap3793_checked
#print axioms fusedMap3793_checked
#print axioms certified3793
def sourceMap3793swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,7,8,9,10,11,12,13] (sourceLabel 7 4 1 v)
def fusedMap3793swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3793swap_checked : acceptsGraphIso
    (source (graph core3793) (root 7) 4 1) DegreeTwoThreeSpectrum2940.graph sourceMap3793swap=true := by decide +kernel
theorem fusedMap3793swap_checked : acceptsGraphIso
    (fused (graph core3793) (root 7) 4 1) DegreeTwoThreeSpectrum2402.graph fusedMap3793swap=true := by decide +kernel
theorem certified3793swap : Certified (graph core3793) (root 7) 4 1 :=
  of_native_maps core3793 DegreeTwoThreeSpectrum2940.graph DegreeTwoThreeSpectrum2402.graph
    sourceMap3793swap fusedMap3793swap sourceMap3793swap_checked fusedMap3793swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3793
#print axioms sourceMap3793swap_checked
#print axioms fusedMap3793swap_checked
#print axioms certified3793swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3505 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap3505 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3505 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3505_checked : acceptsGraphIso
    (source (graph core3505) (root 7) 0 6) DegreeTwoThreeSpectrum4108.graph sourceMap3505=true := by decide +kernel
theorem fusedMap3505_checked : acceptsGraphIso
    (fused (graph core3505) (root 7) 0 6) DegreeTwoThreeSpectrum3873.graph fusedMap3505=true := by decide +kernel
theorem certified3505 : Certified (graph core3505) (root 7) 0 6 :=
  of_native_maps core3505 DegreeTwoThreeSpectrum4108.graph DegreeTwoThreeSpectrum3873.graph
    sourceMap3505 fusedMap3505 sourceMap3505_checked fusedMap3505_checked
    DegreeTwoThreeFiniteComparisons.comparison3505
#print axioms sourceMap3505_checked
#print axioms fusedMap3505_checked
#print axioms certified3505
def sourceMap3505swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3505swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3505swap_checked : acceptsGraphIso
    (source (graph core3505) (root 7) 6 0) DegreeTwoThreeSpectrum4108.graph sourceMap3505swap=true := by decide +kernel
theorem fusedMap3505swap_checked : acceptsGraphIso
    (fused (graph core3505) (root 7) 6 0) DegreeTwoThreeSpectrum3873.graph fusedMap3505swap=true := by decide +kernel
theorem certified3505swap : Certified (graph core3505) (root 7) 6 0 :=
  of_native_maps core3505 DegreeTwoThreeSpectrum4108.graph DegreeTwoThreeSpectrum3873.graph
    sourceMap3505swap fusedMap3505swap sourceMap3505swap_checked fusedMap3505swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3505
#print axioms sourceMap3505swap_checked
#print axioms fusedMap3505swap_checked
#print axioms certified3505swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

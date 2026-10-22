/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3095 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap3095 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3095 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3095_checked : acceptsGraphIso
    (source (graph core3095) (root 6) 0 5) DegreeTwoThreeSpectrum1809.graph sourceMap3095=true := by decide +kernel
theorem fusedMap3095_checked : acceptsGraphIso
    (fused (graph core3095) (root 6) 0 5) DegreeTwoThreeSpectrum1811.graph fusedMap3095=true := by decide +kernel
theorem certified3095 : Certified (graph core3095) (root 6) 0 5 :=
  of_native_maps core3095 DegreeTwoThreeSpectrum1809.graph DegreeTwoThreeSpectrum1811.graph
    sourceMap3095 fusedMap3095 sourceMap3095_checked fusedMap3095_checked
    DegreeTwoThreeFiniteComparisons.comparison3095
#print axioms sourceMap3095_checked
#print axioms fusedMap3095_checked
#print axioms certified3095
def sourceMap3095swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3095swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3095swap_checked : acceptsGraphIso
    (source (graph core3095) (root 6) 5 0) DegreeTwoThreeSpectrum1809.graph sourceMap3095swap=true := by decide +kernel
theorem fusedMap3095swap_checked : acceptsGraphIso
    (fused (graph core3095) (root 6) 5 0) DegreeTwoThreeSpectrum1811.graph fusedMap3095swap=true := by decide +kernel
theorem certified3095swap : Certified (graph core3095) (root 6) 5 0 :=
  of_native_maps core3095 DegreeTwoThreeSpectrum1809.graph DegreeTwoThreeSpectrum1811.graph
    sourceMap3095swap fusedMap3095swap sourceMap3095swap_checked fusedMap3095swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3095
#print axioms sourceMap3095swap_checked
#print axioms fusedMap3095swap_checked
#print axioms certified3095swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

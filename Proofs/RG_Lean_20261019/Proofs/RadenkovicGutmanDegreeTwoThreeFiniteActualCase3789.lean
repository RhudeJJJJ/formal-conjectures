/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3789 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap3789 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3789 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3789_checked : acceptsGraphIso
    (source (graph core3789) (root 6) 1 4) DegreeTwoThreeSpectrum1987.graph sourceMap3789=true := by decide +kernel
theorem fusedMap3789_checked : acceptsGraphIso
    (fused (graph core3789) (root 6) 1 4) DegreeTwoThreeSpectrum1757.graph fusedMap3789=true := by decide +kernel
theorem certified3789 : Certified (graph core3789) (root 6) 1 4 :=
  of_native_maps core3789 DegreeTwoThreeSpectrum1987.graph DegreeTwoThreeSpectrum1757.graph
    sourceMap3789 fusedMap3789 sourceMap3789_checked fusedMap3789_checked
    DegreeTwoThreeFiniteComparisons.comparison3789
#print axioms sourceMap3789_checked
#print axioms fusedMap3789_checked
#print axioms certified3789
def sourceMap3789swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,8,9] (sourceLabel 6 4 1 v)
def fusedMap3789swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3789swap_checked : acceptsGraphIso
    (source (graph core3789) (root 6) 4 1) DegreeTwoThreeSpectrum1987.graph sourceMap3789swap=true := by decide +kernel
theorem fusedMap3789swap_checked : acceptsGraphIso
    (fused (graph core3789) (root 6) 4 1) DegreeTwoThreeSpectrum1757.graph fusedMap3789swap=true := by decide +kernel
theorem certified3789swap : Certified (graph core3789) (root 6) 4 1 :=
  of_native_maps core3789 DegreeTwoThreeSpectrum1987.graph DegreeTwoThreeSpectrum1757.graph
    sourceMap3789swap fusedMap3789swap sourceMap3789swap_checked fusedMap3789swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3789
#print axioms sourceMap3789swap_checked
#print axioms fusedMap3789swap_checked
#print axioms certified3789swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3782 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap3782 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3782 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3782_checked : acceptsGraphIso
    (source (graph core3782) (root 6) 1 4) DegreeTwoThreeSpectrum2098.graph sourceMap3782=true := by decide +kernel
theorem fusedMap3782_checked : acceptsGraphIso
    (fused (graph core3782) (root 6) 1 4) DegreeTwoThreeSpectrum1811.graph fusedMap3782=true := by decide +kernel
theorem certified3782 : Certified (graph core3782) (root 6) 1 4 :=
  of_native_maps core3782 DegreeTwoThreeSpectrum2098.graph DegreeTwoThreeSpectrum1811.graph
    sourceMap3782 fusedMap3782 sourceMap3782_checked fusedMap3782_checked
    DegreeTwoThreeFiniteComparisons.comparison3782
#print axioms sourceMap3782_checked
#print axioms fusedMap3782_checked
#print axioms certified3782
def sourceMap3782swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,7,8] (sourceLabel 6 4 1 v)
def fusedMap3782swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3782swap_checked : acceptsGraphIso
    (source (graph core3782) (root 6) 4 1) DegreeTwoThreeSpectrum2098.graph sourceMap3782swap=true := by decide +kernel
theorem fusedMap3782swap_checked : acceptsGraphIso
    (fused (graph core3782) (root 6) 4 1) DegreeTwoThreeSpectrum1811.graph fusedMap3782swap=true := by decide +kernel
theorem certified3782swap : Certified (graph core3782) (root 6) 4 1 :=
  of_native_maps core3782 DegreeTwoThreeSpectrum2098.graph DegreeTwoThreeSpectrum1811.graph
    sourceMap3782swap fusedMap3782swap sourceMap3782swap_checked fusedMap3782swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3782
#print axioms sourceMap3782swap_checked
#print axioms fusedMap3782swap_checked
#print axioms certified3782swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

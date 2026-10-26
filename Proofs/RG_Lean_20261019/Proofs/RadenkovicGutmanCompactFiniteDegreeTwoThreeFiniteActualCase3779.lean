/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3779 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap3779 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3779 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3779_checked : acceptsGraphIso
    (source (graph core3779) (root 6) 1 4) DegreeTwoThreeSpectrum1973.graph sourceMap3779=true := by decide +kernel
theorem fusedMap3779_checked : acceptsGraphIso
    (fused (graph core3779) (root 6) 1 4) DegreeTwoThreeSpectrum1750.graph fusedMap3779=true := by decide +kernel
theorem certified3779 : Certified (graph core3779) (root 6) 1 4 :=
  of_native_maps core3779 DegreeTwoThreeSpectrum1973.graph DegreeTwoThreeSpectrum1750.graph
    sourceMap3779 fusedMap3779 sourceMap3779_checked fusedMap3779_checked
    DegreeTwoThreeFiniteComparisons.comparison3779
#print axioms sourceMap3779_checked
#print axioms fusedMap3779_checked
#print axioms certified3779
def sourceMap3779swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,7,8] (sourceLabel 6 4 1 v)
def fusedMap3779swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3779swap_checked : acceptsGraphIso
    (source (graph core3779) (root 6) 4 1) DegreeTwoThreeSpectrum1973.graph sourceMap3779swap=true := by decide +kernel
theorem fusedMap3779swap_checked : acceptsGraphIso
    (fused (graph core3779) (root 6) 4 1) DegreeTwoThreeSpectrum1750.graph fusedMap3779swap=true := by decide +kernel
theorem certified3779swap : Certified (graph core3779) (root 6) 4 1 :=
  of_native_maps core3779 DegreeTwoThreeSpectrum1973.graph DegreeTwoThreeSpectrum1750.graph
    sourceMap3779swap fusedMap3779swap sourceMap3779swap_checked fusedMap3779swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3779
#print axioms sourceMap3779swap_checked
#print axioms fusedMap3779swap_checked
#print axioms certified3779swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

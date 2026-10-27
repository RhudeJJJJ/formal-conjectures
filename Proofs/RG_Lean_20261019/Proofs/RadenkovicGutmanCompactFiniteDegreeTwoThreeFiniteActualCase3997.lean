/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3997 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3997 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 5 1 6 v)
def fusedMap3997 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 1 6 v)
theorem sourceMap3997_checked : acceptsGraphIso
    (source (graph core3997) (root 5) 1 6) DegreeTwoThreeSpectrum2506.graph sourceMap3997=true := by decide +kernel
theorem fusedMap3997_checked : acceptsGraphIso
    (fused (graph core3997) (root 5) 1 6) DegreeTwoThreeSpectrum2321.graph fusedMap3997=true := by decide +kernel
theorem certified3997 : Certified (graph core3997) (root 5) 1 6 :=
  of_native_maps core3997 DegreeTwoThreeSpectrum2506.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap3997 fusedMap3997 sourceMap3997_checked fusedMap3997_checked
    DegreeTwoThreeFiniteComparisons.comparison3997
#print axioms sourceMap3997_checked
#print axioms fusedMap3997_checked
#print axioms certified3997
def sourceMap3997swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,10,11,12,13,14,8,9] (sourceLabel 5 6 1 v)
def fusedMap3997swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 6 1 v)
theorem sourceMap3997swap_checked : acceptsGraphIso
    (source (graph core3997) (root 5) 6 1) DegreeTwoThreeSpectrum2506.graph sourceMap3997swap=true := by decide +kernel
theorem fusedMap3997swap_checked : acceptsGraphIso
    (fused (graph core3997) (root 5) 6 1) DegreeTwoThreeSpectrum2321.graph fusedMap3997swap=true := by decide +kernel
theorem certified3997swap : Certified (graph core3997) (root 5) 6 1 :=
  of_native_maps core3997 DegreeTwoThreeSpectrum2506.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap3997swap fusedMap3997swap sourceMap3997swap_checked fusedMap3997swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3997
#print axioms sourceMap3997swap_checked
#print axioms fusedMap3997swap_checked
#print axioms certified3997swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

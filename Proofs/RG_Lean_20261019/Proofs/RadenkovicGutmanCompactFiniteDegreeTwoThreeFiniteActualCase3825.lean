/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3825 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap3825 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3825 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3825_checked : acceptsGraphIso
    (source (graph core3825) (root 7) 1 4) DegreeTwoThreeSpectrum3023.graph sourceMap3825=true := by decide +kernel
theorem fusedMap3825_checked : acceptsGraphIso
    (fused (graph core3825) (root 7) 1 4) DegreeTwoThreeSpectrum2440.graph fusedMap3825=true := by decide +kernel
theorem certified3825 : Certified (graph core3825) (root 7) 1 4 :=
  of_native_maps core3825 DegreeTwoThreeSpectrum3023.graph DegreeTwoThreeSpectrum2440.graph
    sourceMap3825 fusedMap3825 sourceMap3825_checked fusedMap3825_checked
    DegreeTwoThreeFiniteComparisons.comparison3825
#print axioms sourceMap3825_checked
#print axioms fusedMap3825_checked
#print axioms certified3825
def sourceMap3825swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3825swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3825swap_checked : acceptsGraphIso
    (source (graph core3825) (root 7) 4 1) DegreeTwoThreeSpectrum3023.graph sourceMap3825swap=true := by decide +kernel
theorem fusedMap3825swap_checked : acceptsGraphIso
    (fused (graph core3825) (root 7) 4 1) DegreeTwoThreeSpectrum2440.graph fusedMap3825swap=true := by decide +kernel
theorem certified3825swap : Certified (graph core3825) (root 7) 4 1 :=
  of_native_maps core3825 DegreeTwoThreeSpectrum3023.graph DegreeTwoThreeSpectrum2440.graph
    sourceMap3825swap fusedMap3825swap sourceMap3825swap_checked fusedMap3825swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3825
#print axioms sourceMap3825swap_checked
#print axioms fusedMap3825swap_checked
#print axioms certified3825swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

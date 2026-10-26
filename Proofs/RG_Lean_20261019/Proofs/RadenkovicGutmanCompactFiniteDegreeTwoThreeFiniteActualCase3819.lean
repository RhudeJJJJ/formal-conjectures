/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3819 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap3819 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3819 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3819_checked : acceptsGraphIso
    (source (graph core3819) (root 7) 1 4) DegreeTwoThreeSpectrum3474.graph sourceMap3819=true := by decide +kernel
theorem fusedMap3819_checked : acceptsGraphIso
    (fused (graph core3819) (root 7) 1 4) DegreeTwoThreeSpectrum2695.graph fusedMap3819=true := by decide +kernel
theorem certified3819 : Certified (graph core3819) (root 7) 1 4 :=
  of_native_maps core3819 DegreeTwoThreeSpectrum3474.graph DegreeTwoThreeSpectrum2695.graph
    sourceMap3819 fusedMap3819 sourceMap3819_checked fusedMap3819_checked
    DegreeTwoThreeFiniteComparisons.comparison3819
#print axioms sourceMap3819_checked
#print axioms fusedMap3819_checked
#print axioms certified3819
def sourceMap3819swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3819swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3819swap_checked : acceptsGraphIso
    (source (graph core3819) (root 7) 4 1) DegreeTwoThreeSpectrum3474.graph sourceMap3819swap=true := by decide +kernel
theorem fusedMap3819swap_checked : acceptsGraphIso
    (fused (graph core3819) (root 7) 4 1) DegreeTwoThreeSpectrum2695.graph fusedMap3819swap=true := by decide +kernel
theorem certified3819swap : Certified (graph core3819) (root 7) 4 1 :=
  of_native_maps core3819 DegreeTwoThreeSpectrum3474.graph DegreeTwoThreeSpectrum2695.graph
    sourceMap3819swap fusedMap3819swap sourceMap3819swap_checked fusedMap3819swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3819
#print axioms sourceMap3819swap_checked
#print axioms fusedMap3819swap_checked
#print axioms certified3819swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

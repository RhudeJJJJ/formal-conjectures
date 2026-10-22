/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3138 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap3138 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3138 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3138_checked : acceptsGraphIso
    (source (graph core3138) (root 7) 0 5) DegreeTwoThreeSpectrum3025.graph sourceMap3138=true := by decide +kernel
theorem fusedMap3138_checked : acceptsGraphIso
    (fused (graph core3138) (root 7) 0 5) DegreeTwoThreeSpectrum2440.graph fusedMap3138=true := by decide +kernel
theorem certified3138 : Certified (graph core3138) (root 7) 0 5 :=
  of_native_maps core3138 DegreeTwoThreeSpectrum3025.graph DegreeTwoThreeSpectrum2440.graph
    sourceMap3138 fusedMap3138 sourceMap3138_checked fusedMap3138_checked
    DegreeTwoThreeFiniteComparisons.comparison3138
#print axioms sourceMap3138_checked
#print axioms fusedMap3138_checked
#print axioms certified3138
def sourceMap3138swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,10] (sourceLabel 7 5 0 v)
def fusedMap3138swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3138swap_checked : acceptsGraphIso
    (source (graph core3138) (root 7) 5 0) DegreeTwoThreeSpectrum3025.graph sourceMap3138swap=true := by decide +kernel
theorem fusedMap3138swap_checked : acceptsGraphIso
    (fused (graph core3138) (root 7) 5 0) DegreeTwoThreeSpectrum2440.graph fusedMap3138swap=true := by decide +kernel
theorem certified3138swap : Certified (graph core3138) (root 7) 5 0 :=
  of_native_maps core3138 DegreeTwoThreeSpectrum3025.graph DegreeTwoThreeSpectrum2440.graph
    sourceMap3138swap fusedMap3138swap sourceMap3138swap_checked fusedMap3138swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3138
#print axioms sourceMap3138swap_checked
#print axioms fusedMap3138swap_checked
#print axioms certified3138swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

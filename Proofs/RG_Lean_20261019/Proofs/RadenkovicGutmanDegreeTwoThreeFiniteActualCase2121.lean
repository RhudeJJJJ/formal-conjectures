/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2121 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap2121 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2121 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 0 4 v)
theorem sourceMap2121_checked : acceptsGraphIso
    (source (graph core2121) (root 8) 0 4) DegreeTwoThreeSpectrum2379.graph sourceMap2121=true := by decide +kernel
theorem fusedMap2121_checked : acceptsGraphIso
    (fused (graph core2121) (root 8) 0 4) DegreeTwoThreeSpectrum2380.graph fusedMap2121=true := by decide +kernel
theorem certified2121 : Certified (graph core2121) (root 8) 0 4 :=
  of_native_maps core2121 DegreeTwoThreeSpectrum2379.graph DegreeTwoThreeSpectrum2380.graph
    sourceMap2121 fusedMap2121 sourceMap2121_checked fusedMap2121_checked
    DegreeTwoThreeFiniteComparisons.comparison2121
#print axioms sourceMap2121_checked
#print axioms fusedMap2121_checked
#print axioms certified2121
def sourceMap2121swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2121swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 4 0 v)
theorem sourceMap2121swap_checked : acceptsGraphIso
    (source (graph core2121) (root 8) 4 0) DegreeTwoThreeSpectrum2379.graph sourceMap2121swap=true := by decide +kernel
theorem fusedMap2121swap_checked : acceptsGraphIso
    (fused (graph core2121) (root 8) 4 0) DegreeTwoThreeSpectrum2380.graph fusedMap2121swap=true := by decide +kernel
theorem certified2121swap : Certified (graph core2121) (root 8) 4 0 :=
  of_native_maps core2121 DegreeTwoThreeSpectrum2379.graph DegreeTwoThreeSpectrum2380.graph
    sourceMap2121swap fusedMap2121swap sourceMap2121swap_checked fusedMap2121swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2121
#print axioms sourceMap2121swap_checked
#print axioms fusedMap2121swap_checked
#print axioms certified2121swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

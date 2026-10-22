/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2141 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap2141 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2141 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2141_checked : acceptsGraphIso
    (source (graph core2141) (root 8) 0 4) DegreeTwoThreeSpectrum2986.graph sourceMap2141=true := by decide +kernel
theorem fusedMap2141_checked : acceptsGraphIso
    (fused (graph core2141) (root 8) 0 4) DegreeTwoThreeSpectrum2415.graph fusedMap2141=true := by decide +kernel
theorem certified2141 : Certified (graph core2141) (root 8) 0 4 :=
  of_native_maps core2141 DegreeTwoThreeSpectrum2986.graph DegreeTwoThreeSpectrum2415.graph
    sourceMap2141 fusedMap2141 sourceMap2141_checked fusedMap2141_checked
    DegreeTwoThreeFiniteComparisons.comparison2141
#print axioms sourceMap2141_checked
#print axioms fusedMap2141_checked
#print axioms certified2141
def sourceMap2141swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2141swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2141swap_checked : acceptsGraphIso
    (source (graph core2141) (root 8) 4 0) DegreeTwoThreeSpectrum2986.graph sourceMap2141swap=true := by decide +kernel
theorem fusedMap2141swap_checked : acceptsGraphIso
    (fused (graph core2141) (root 8) 4 0) DegreeTwoThreeSpectrum2415.graph fusedMap2141swap=true := by decide +kernel
theorem certified2141swap : Certified (graph core2141) (root 8) 4 0 :=
  of_native_maps core2141 DegreeTwoThreeSpectrum2986.graph DegreeTwoThreeSpectrum2415.graph
    sourceMap2141swap fusedMap2141swap sourceMap2141swap_checked fusedMap2141swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2141
#print axioms sourceMap2141swap_checked
#print axioms fusedMap2141swap_checked
#print axioms certified2141swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2134 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap2134 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2134 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2134_checked : acceptsGraphIso
    (source (graph core2134) (root 8) 0 4) DegreeTwoThreeSpectrum2795.graph sourceMap2134=true := by decide +kernel
theorem fusedMap2134_checked : acceptsGraphIso
    (fused (graph core2134) (root 8) 0 4) DegreeTwoThreeSpectrum2368.graph fusedMap2134=true := by decide +kernel
theorem certified2134 : Certified (graph core2134) (root 8) 0 4 :=
  of_native_maps core2134 DegreeTwoThreeSpectrum2795.graph DegreeTwoThreeSpectrum2368.graph
    sourceMap2134 fusedMap2134 sourceMap2134_checked fusedMap2134_checked
    DegreeTwoThreeFiniteComparisons.comparison2134
#print axioms sourceMap2134_checked
#print axioms fusedMap2134_checked
#print axioms certified2134
def sourceMap2134swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2134swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2134swap_checked : acceptsGraphIso
    (source (graph core2134) (root 8) 4 0) DegreeTwoThreeSpectrum2795.graph sourceMap2134swap=true := by decide +kernel
theorem fusedMap2134swap_checked : acceptsGraphIso
    (fused (graph core2134) (root 8) 4 0) DegreeTwoThreeSpectrum2368.graph fusedMap2134swap=true := by decide +kernel
theorem certified2134swap : Certified (graph core2134) (root 8) 4 0 :=
  of_native_maps core2134 DegreeTwoThreeSpectrum2795.graph DegreeTwoThreeSpectrum2368.graph
    sourceMap2134swap fusedMap2134swap sourceMap2134swap_checked fusedMap2134swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2134
#print axioms sourceMap2134swap_checked
#print axioms fusedMap2134swap_checked
#print axioms certified2134swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

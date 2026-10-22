/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2158 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap2158 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2158 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2158_checked : acceptsGraphIso
    (source (graph core2158) (root 8) 0 4) DegreeTwoThreeSpectrum2655.graph sourceMap2158=true := by decide +kernel
theorem fusedMap2158_checked : acceptsGraphIso
    (fused (graph core2158) (root 8) 0 4) DegreeTwoThreeSpectrum2657.graph fusedMap2158=true := by decide +kernel
theorem certified2158 : Certified (graph core2158) (root 8) 0 4 :=
  of_native_maps core2158 DegreeTwoThreeSpectrum2655.graph DegreeTwoThreeSpectrum2657.graph
    sourceMap2158 fusedMap2158 sourceMap2158_checked fusedMap2158_checked
    DegreeTwoThreeFiniteComparisons.comparison2158
#print axioms sourceMap2158_checked
#print axioms fusedMap2158_checked
#print axioms certified2158
def sourceMap2158swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2158swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2158swap_checked : acceptsGraphIso
    (source (graph core2158) (root 8) 4 0) DegreeTwoThreeSpectrum2655.graph sourceMap2158swap=true := by decide +kernel
theorem fusedMap2158swap_checked : acceptsGraphIso
    (fused (graph core2158) (root 8) 4 0) DegreeTwoThreeSpectrum2657.graph fusedMap2158swap=true := by decide +kernel
theorem certified2158swap : Certified (graph core2158) (root 8) 4 0 :=
  of_native_maps core2158 DegreeTwoThreeSpectrum2655.graph DegreeTwoThreeSpectrum2657.graph
    sourceMap2158swap fusedMap2158swap sourceMap2158swap_checked fusedMap2158swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2158
#print axioms sourceMap2158swap_checked
#print axioms fusedMap2158swap_checked
#print axioms certified2158swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

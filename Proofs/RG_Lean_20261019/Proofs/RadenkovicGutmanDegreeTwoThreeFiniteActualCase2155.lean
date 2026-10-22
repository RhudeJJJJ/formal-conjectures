/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2155 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap2155 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2155 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2155_checked : acceptsGraphIso
    (source (graph core2155) (root 8) 0 4) DegreeTwoThreeSpectrum2586.graph sourceMap2155=true := by decide +kernel
theorem fusedMap2155_checked : acceptsGraphIso
    (fused (graph core2155) (root 8) 0 4) DegreeTwoThreeSpectrum2588.graph fusedMap2155=true := by decide +kernel
theorem certified2155 : Certified (graph core2155) (root 8) 0 4 :=
  of_native_maps core2155 DegreeTwoThreeSpectrum2586.graph DegreeTwoThreeSpectrum2588.graph
    sourceMap2155 fusedMap2155 sourceMap2155_checked fusedMap2155_checked
    DegreeTwoThreeFiniteComparisons.comparison2155
#print axioms sourceMap2155_checked
#print axioms fusedMap2155_checked
#print axioms certified2155
def sourceMap2155swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2155swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2155swap_checked : acceptsGraphIso
    (source (graph core2155) (root 8) 4 0) DegreeTwoThreeSpectrum2586.graph sourceMap2155swap=true := by decide +kernel
theorem fusedMap2155swap_checked : acceptsGraphIso
    (fused (graph core2155) (root 8) 4 0) DegreeTwoThreeSpectrum2588.graph fusedMap2155swap=true := by decide +kernel
theorem certified2155swap : Certified (graph core2155) (root 8) 4 0 :=
  of_native_maps core2155 DegreeTwoThreeSpectrum2586.graph DegreeTwoThreeSpectrum2588.graph
    sourceMap2155swap fusedMap2155swap sourceMap2155swap_checked fusedMap2155swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2155
#print axioms sourceMap2155swap_checked
#print axioms fusedMap2155swap_checked
#print axioms certified2155swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

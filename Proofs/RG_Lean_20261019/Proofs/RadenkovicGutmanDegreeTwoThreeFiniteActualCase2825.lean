/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2825 : Family 10 := level10.get ⟨1140,by decide⟩
def sourceMap2825 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2825 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2825_checked : acceptsGraphIso
    (source (graph core2825) (root 10) 0 4) DegreeTwoThreeSpectrum6266.graph sourceMap2825=true := by decide +kernel
theorem fusedMap2825_checked : acceptsGraphIso
    (fused (graph core2825) (root 10) 0 4) DegreeTwoThreeSpectrum6267.graph fusedMap2825=true := by decide +kernel
theorem certified2825 : Certified (graph core2825) (root 10) 0 4 :=
  of_native_maps core2825 DegreeTwoThreeSpectrum6266.graph DegreeTwoThreeSpectrum6267.graph
    sourceMap2825 fusedMap2825 sourceMap2825_checked fusedMap2825_checked
    DegreeTwoThreeFiniteComparisons.comparison2825
#print axioms sourceMap2825_checked
#print axioms fusedMap2825_checked
#print axioms certified2825
def sourceMap2825swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2825swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2825swap_checked : acceptsGraphIso
    (source (graph core2825) (root 10) 4 0) DegreeTwoThreeSpectrum6266.graph sourceMap2825swap=true := by decide +kernel
theorem fusedMap2825swap_checked : acceptsGraphIso
    (fused (graph core2825) (root 10) 4 0) DegreeTwoThreeSpectrum6267.graph fusedMap2825swap=true := by decide +kernel
theorem certified2825swap : Certified (graph core2825) (root 10) 4 0 :=
  of_native_maps core2825 DegreeTwoThreeSpectrum6266.graph DegreeTwoThreeSpectrum6267.graph
    sourceMap2825swap fusedMap2825swap sourceMap2825swap_checked fusedMap2825swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2825
#print axioms sourceMap2825swap_checked
#print axioms fusedMap2825swap_checked
#print axioms certified2825swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

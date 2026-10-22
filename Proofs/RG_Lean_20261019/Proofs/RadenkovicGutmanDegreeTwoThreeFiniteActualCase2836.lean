/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2836 : Family 10 := level10.get ⟨1166,by decide⟩
def sourceMap2836 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2836 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2836_checked : acceptsGraphIso
    (source (graph core2836) (root 10) 0 4) DegreeTwoThreeSpectrum6315.graph sourceMap2836=true := by decide +kernel
theorem fusedMap2836_checked : acceptsGraphIso
    (fused (graph core2836) (root 10) 0 4) DegreeTwoThreeSpectrum6316.graph fusedMap2836=true := by decide +kernel
theorem certified2836 : Certified (graph core2836) (root 10) 0 4 :=
  of_native_maps core2836 DegreeTwoThreeSpectrum6315.graph DegreeTwoThreeSpectrum6316.graph
    sourceMap2836 fusedMap2836 sourceMap2836_checked fusedMap2836_checked
    DegreeTwoThreeFiniteComparisons.comparison2836
#print axioms sourceMap2836_checked
#print axioms fusedMap2836_checked
#print axioms certified2836
def sourceMap2836swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2836swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2836swap_checked : acceptsGraphIso
    (source (graph core2836) (root 10) 4 0) DegreeTwoThreeSpectrum6315.graph sourceMap2836swap=true := by decide +kernel
theorem fusedMap2836swap_checked : acceptsGraphIso
    (fused (graph core2836) (root 10) 4 0) DegreeTwoThreeSpectrum6316.graph fusedMap2836swap=true := by decide +kernel
theorem certified2836swap : Certified (graph core2836) (root 10) 4 0 :=
  of_native_maps core2836 DegreeTwoThreeSpectrum6315.graph DegreeTwoThreeSpectrum6316.graph
    sourceMap2836swap fusedMap2836swap sourceMap2836swap_checked fusedMap2836swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2836
#print axioms sourceMap2836swap_checked
#print axioms fusedMap2836swap_checked
#print axioms certified2836swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

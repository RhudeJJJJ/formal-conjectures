/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2829 : Family 10 := level10.get ⟨1152,by decide⟩
def sourceMap2829 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2829 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2829_checked : acceptsGraphIso
    (source (graph core2829) (root 10) 0 4) DegreeTwoThreeSpectrum6293.graph sourceMap2829=true := by decide +kernel
theorem fusedMap2829_checked : acceptsGraphIso
    (fused (graph core2829) (root 10) 0 4) DegreeTwoThreeSpectrum6294.graph fusedMap2829=true := by decide +kernel
theorem certified2829 : Certified (graph core2829) (root 10) 0 4 :=
  of_native_maps core2829 DegreeTwoThreeSpectrum6293.graph DegreeTwoThreeSpectrum6294.graph
    sourceMap2829 fusedMap2829 sourceMap2829_checked fusedMap2829_checked
    DegreeTwoThreeFiniteComparisons.comparison2829
#print axioms sourceMap2829_checked
#print axioms fusedMap2829_checked
#print axioms certified2829
def sourceMap2829swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2829swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2829swap_checked : acceptsGraphIso
    (source (graph core2829) (root 10) 4 0) DegreeTwoThreeSpectrum6293.graph sourceMap2829swap=true := by decide +kernel
theorem fusedMap2829swap_checked : acceptsGraphIso
    (fused (graph core2829) (root 10) 4 0) DegreeTwoThreeSpectrum6294.graph fusedMap2829swap=true := by decide +kernel
theorem certified2829swap : Certified (graph core2829) (root 10) 4 0 :=
  of_native_maps core2829 DegreeTwoThreeSpectrum6293.graph DegreeTwoThreeSpectrum6294.graph
    sourceMap2829swap fusedMap2829swap sourceMap2829swap_checked fusedMap2829swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2829
#print axioms sourceMap2829swap_checked
#print axioms fusedMap2829swap_checked
#print axioms certified2829swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

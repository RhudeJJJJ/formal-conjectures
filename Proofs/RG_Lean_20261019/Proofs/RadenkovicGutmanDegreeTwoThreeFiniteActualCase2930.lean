/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2930 : Family 10 := level10.get ⟨1387,by decide⟩
def sourceMap2930 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2930 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2930_checked : acceptsGraphIso
    (source (graph core2930) (root 10) 0 4) DegreeTwoThreeSpectrum6747.graph sourceMap2930=true := by decide +kernel
theorem fusedMap2930_checked : acceptsGraphIso
    (fused (graph core2930) (root 10) 0 4) DegreeTwoThreeSpectrum6748.graph fusedMap2930=true := by decide +kernel
theorem certified2930 : Certified (graph core2930) (root 10) 0 4 :=
  of_native_maps core2930 DegreeTwoThreeSpectrum6747.graph DegreeTwoThreeSpectrum6748.graph
    sourceMap2930 fusedMap2930 sourceMap2930_checked fusedMap2930_checked
    DegreeTwoThreeFiniteComparisons.comparison2930
#print axioms sourceMap2930_checked
#print axioms fusedMap2930_checked
#print axioms certified2930
def sourceMap2930swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2930swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2930swap_checked : acceptsGraphIso
    (source (graph core2930) (root 10) 4 0) DegreeTwoThreeSpectrum6747.graph sourceMap2930swap=true := by decide +kernel
theorem fusedMap2930swap_checked : acceptsGraphIso
    (fused (graph core2930) (root 10) 4 0) DegreeTwoThreeSpectrum6748.graph fusedMap2930swap=true := by decide +kernel
theorem certified2930swap : Certified (graph core2930) (root 10) 4 0 :=
  of_native_maps core2930 DegreeTwoThreeSpectrum6747.graph DegreeTwoThreeSpectrum6748.graph
    sourceMap2930swap fusedMap2930swap sourceMap2930swap_checked fusedMap2930swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2930
#print axioms sourceMap2930swap_checked
#print axioms fusedMap2930swap_checked
#print axioms certified2930swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

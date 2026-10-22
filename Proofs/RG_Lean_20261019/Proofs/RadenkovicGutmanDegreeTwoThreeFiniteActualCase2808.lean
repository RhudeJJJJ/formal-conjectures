/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2808 : Family 10 := level10.get ⟨1097,by decide⟩
def sourceMap2808 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2808 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2808_checked : acceptsGraphIso
    (source (graph core2808) (root 10) 0 4) DegreeTwoThreeSpectrum6177.graph sourceMap2808=true := by decide +kernel
theorem fusedMap2808_checked : acceptsGraphIso
    (fused (graph core2808) (root 10) 0 4) DegreeTwoThreeSpectrum6178.graph fusedMap2808=true := by decide +kernel
theorem certified2808 : Certified (graph core2808) (root 10) 0 4 :=
  of_native_maps core2808 DegreeTwoThreeSpectrum6177.graph DegreeTwoThreeSpectrum6178.graph
    sourceMap2808 fusedMap2808 sourceMap2808_checked fusedMap2808_checked
    DegreeTwoThreeFiniteComparisons.comparison2808
#print axioms sourceMap2808_checked
#print axioms fusedMap2808_checked
#print axioms certified2808
def sourceMap2808swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2808swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2808swap_checked : acceptsGraphIso
    (source (graph core2808) (root 10) 4 0) DegreeTwoThreeSpectrum6177.graph sourceMap2808swap=true := by decide +kernel
theorem fusedMap2808swap_checked : acceptsGraphIso
    (fused (graph core2808) (root 10) 4 0) DegreeTwoThreeSpectrum6178.graph fusedMap2808swap=true := by decide +kernel
theorem certified2808swap : Certified (graph core2808) (root 10) 4 0 :=
  of_native_maps core2808 DegreeTwoThreeSpectrum6177.graph DegreeTwoThreeSpectrum6178.graph
    sourceMap2808swap fusedMap2808swap sourceMap2808swap_checked fusedMap2808swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2808
#print axioms sourceMap2808swap_checked
#print axioms fusedMap2808swap_checked
#print axioms certified2808swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

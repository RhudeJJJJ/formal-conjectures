/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2872 : Family 10 := level10.get ⟨1254,by decide⟩
def sourceMap2872 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2872 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2872_checked : acceptsGraphIso
    (source (graph core2872) (root 10) 0 4) DegreeTwoThreeSpectrum6497.graph sourceMap2872=true := by decide +kernel
theorem fusedMap2872_checked : acceptsGraphIso
    (fused (graph core2872) (root 10) 0 4) DegreeTwoThreeSpectrum6498.graph fusedMap2872=true := by decide +kernel
theorem certified2872 : Certified (graph core2872) (root 10) 0 4 :=
  of_native_maps core2872 DegreeTwoThreeSpectrum6497.graph DegreeTwoThreeSpectrum6498.graph
    sourceMap2872 fusedMap2872 sourceMap2872_checked fusedMap2872_checked
    DegreeTwoThreeFiniteComparisons.comparison2872
#print axioms sourceMap2872_checked
#print axioms fusedMap2872_checked
#print axioms certified2872
def sourceMap2872swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2872swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2872swap_checked : acceptsGraphIso
    (source (graph core2872) (root 10) 4 0) DegreeTwoThreeSpectrum6497.graph sourceMap2872swap=true := by decide +kernel
theorem fusedMap2872swap_checked : acceptsGraphIso
    (fused (graph core2872) (root 10) 4 0) DegreeTwoThreeSpectrum6498.graph fusedMap2872swap=true := by decide +kernel
theorem certified2872swap : Certified (graph core2872) (root 10) 4 0 :=
  of_native_maps core2872 DegreeTwoThreeSpectrum6497.graph DegreeTwoThreeSpectrum6498.graph
    sourceMap2872swap fusedMap2872swap sourceMap2872swap_checked fusedMap2872swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2872
#print axioms sourceMap2872swap_checked
#print axioms fusedMap2872swap_checked
#print axioms certified2872swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

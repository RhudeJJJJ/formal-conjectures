/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2873 : Family 10 := level10.get ⟨1255,by decide⟩
def sourceMap2873 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2873 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2873_checked : acceptsGraphIso
    (source (graph core2873) (root 10) 0 4) DegreeTwoThreeSpectrum6499.graph sourceMap2873=true := by decide +kernel
theorem fusedMap2873_checked : acceptsGraphIso
    (fused (graph core2873) (root 10) 0 4) DegreeTwoThreeSpectrum6500.graph fusedMap2873=true := by decide +kernel
theorem certified2873 : Certified (graph core2873) (root 10) 0 4 :=
  of_native_maps core2873 DegreeTwoThreeSpectrum6499.graph DegreeTwoThreeSpectrum6500.graph
    sourceMap2873 fusedMap2873 sourceMap2873_checked fusedMap2873_checked
    DegreeTwoThreeFiniteComparisons.comparison2873
#print axioms sourceMap2873_checked
#print axioms fusedMap2873_checked
#print axioms certified2873
def sourceMap2873swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2873swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2873swap_checked : acceptsGraphIso
    (source (graph core2873) (root 10) 4 0) DegreeTwoThreeSpectrum6499.graph sourceMap2873swap=true := by decide +kernel
theorem fusedMap2873swap_checked : acceptsGraphIso
    (fused (graph core2873) (root 10) 4 0) DegreeTwoThreeSpectrum6500.graph fusedMap2873swap=true := by decide +kernel
theorem certified2873swap : Certified (graph core2873) (root 10) 4 0 :=
  of_native_maps core2873 DegreeTwoThreeSpectrum6499.graph DegreeTwoThreeSpectrum6500.graph
    sourceMap2873swap fusedMap2873swap sourceMap2873swap_checked fusedMap2873swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2873
#print axioms sourceMap2873swap_checked
#print axioms fusedMap2873swap_checked
#print axioms certified2873swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

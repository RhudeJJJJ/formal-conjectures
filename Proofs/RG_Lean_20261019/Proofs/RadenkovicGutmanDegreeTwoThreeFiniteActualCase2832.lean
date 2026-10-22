/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2832 : Family 10 := level10.get ⟨1159,by decide⟩
def sourceMap2832 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2832 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2832_checked : acceptsGraphIso
    (source (graph core2832) (root 10) 0 4) DegreeTwoThreeSpectrum6301.graph sourceMap2832=true := by decide +kernel
theorem fusedMap2832_checked : acceptsGraphIso
    (fused (graph core2832) (root 10) 0 4) DegreeTwoThreeSpectrum6302.graph fusedMap2832=true := by decide +kernel
theorem certified2832 : Certified (graph core2832) (root 10) 0 4 :=
  of_native_maps core2832 DegreeTwoThreeSpectrum6301.graph DegreeTwoThreeSpectrum6302.graph
    sourceMap2832 fusedMap2832 sourceMap2832_checked fusedMap2832_checked
    DegreeTwoThreeFiniteComparisons.comparison2832
#print axioms sourceMap2832_checked
#print axioms fusedMap2832_checked
#print axioms certified2832
def sourceMap2832swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2832swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2832swap_checked : acceptsGraphIso
    (source (graph core2832) (root 10) 4 0) DegreeTwoThreeSpectrum6301.graph sourceMap2832swap=true := by decide +kernel
theorem fusedMap2832swap_checked : acceptsGraphIso
    (fused (graph core2832) (root 10) 4 0) DegreeTwoThreeSpectrum6302.graph fusedMap2832swap=true := by decide +kernel
theorem certified2832swap : Certified (graph core2832) (root 10) 4 0 :=
  of_native_maps core2832 DegreeTwoThreeSpectrum6301.graph DegreeTwoThreeSpectrum6302.graph
    sourceMap2832swap fusedMap2832swap sourceMap2832swap_checked fusedMap2832swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2832
#print axioms sourceMap2832swap_checked
#print axioms fusedMap2832swap_checked
#print axioms certified2832swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

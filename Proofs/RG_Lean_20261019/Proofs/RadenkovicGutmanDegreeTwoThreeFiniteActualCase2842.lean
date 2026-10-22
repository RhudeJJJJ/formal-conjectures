/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2842 : Family 10 := level10.get ⟨1183,by decide⟩
def sourceMap2842 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2842 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2842_checked : acceptsGraphIso
    (source (graph core2842) (root 10) 0 4) DegreeTwoThreeSpectrum6350.graph sourceMap2842=true := by decide +kernel
theorem fusedMap2842_checked : acceptsGraphIso
    (fused (graph core2842) (root 10) 0 4) DegreeTwoThreeSpectrum6351.graph fusedMap2842=true := by decide +kernel
theorem certified2842 : Certified (graph core2842) (root 10) 0 4 :=
  of_native_maps core2842 DegreeTwoThreeSpectrum6350.graph DegreeTwoThreeSpectrum6351.graph
    sourceMap2842 fusedMap2842 sourceMap2842_checked fusedMap2842_checked
    DegreeTwoThreeFiniteComparisons.comparison2842
#print axioms sourceMap2842_checked
#print axioms fusedMap2842_checked
#print axioms certified2842
def sourceMap2842swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2842swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2842swap_checked : acceptsGraphIso
    (source (graph core2842) (root 10) 4 0) DegreeTwoThreeSpectrum6350.graph sourceMap2842swap=true := by decide +kernel
theorem fusedMap2842swap_checked : acceptsGraphIso
    (fused (graph core2842) (root 10) 4 0) DegreeTwoThreeSpectrum6351.graph fusedMap2842swap=true := by decide +kernel
theorem certified2842swap : Certified (graph core2842) (root 10) 4 0 :=
  of_native_maps core2842 DegreeTwoThreeSpectrum6350.graph DegreeTwoThreeSpectrum6351.graph
    sourceMap2842swap fusedMap2842swap sourceMap2842swap_checked fusedMap2842swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2842
#print axioms sourceMap2842swap_checked
#print axioms fusedMap2842swap_checked
#print axioms certified2842swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

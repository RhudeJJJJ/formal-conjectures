/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2817 : Family 10 := level10.get ⟨1120,by decide⟩
def sourceMap2817 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2817 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2817_checked : acceptsGraphIso
    (source (graph core2817) (root 10) 0 4) DegreeTwoThreeSpectrum6225.graph sourceMap2817=true := by decide +kernel
theorem fusedMap2817_checked : acceptsGraphIso
    (fused (graph core2817) (root 10) 0 4) DegreeTwoThreeSpectrum6226.graph fusedMap2817=true := by decide +kernel
theorem certified2817 : Certified (graph core2817) (root 10) 0 4 :=
  of_native_maps core2817 DegreeTwoThreeSpectrum6225.graph DegreeTwoThreeSpectrum6226.graph
    sourceMap2817 fusedMap2817 sourceMap2817_checked fusedMap2817_checked
    DegreeTwoThreeFiniteComparisons.comparison2817
#print axioms sourceMap2817_checked
#print axioms fusedMap2817_checked
#print axioms certified2817
def sourceMap2817swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2817swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2817swap_checked : acceptsGraphIso
    (source (graph core2817) (root 10) 4 0) DegreeTwoThreeSpectrum6225.graph sourceMap2817swap=true := by decide +kernel
theorem fusedMap2817swap_checked : acceptsGraphIso
    (fused (graph core2817) (root 10) 4 0) DegreeTwoThreeSpectrum6226.graph fusedMap2817swap=true := by decide +kernel
theorem certified2817swap : Certified (graph core2817) (root 10) 4 0 :=
  of_native_maps core2817 DegreeTwoThreeSpectrum6225.graph DegreeTwoThreeSpectrum6226.graph
    sourceMap2817swap fusedMap2817swap sourceMap2817swap_checked fusedMap2817swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2817
#print axioms sourceMap2817swap_checked
#print axioms fusedMap2817swap_checked
#print axioms certified2817swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

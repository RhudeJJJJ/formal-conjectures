/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2839 : Family 10 := level10.get ⟨1170,by decide⟩
def sourceMap2839 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2839 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2839_checked : acceptsGraphIso
    (source (graph core2839) (root 10) 0 4) DegreeTwoThreeSpectrum6323.graph sourceMap2839=true := by decide +kernel
theorem fusedMap2839_checked : acceptsGraphIso
    (fused (graph core2839) (root 10) 0 4) DegreeTwoThreeSpectrum6324.graph fusedMap2839=true := by decide +kernel
theorem certified2839 : Certified (graph core2839) (root 10) 0 4 :=
  of_native_maps core2839 DegreeTwoThreeSpectrum6323.graph DegreeTwoThreeSpectrum6324.graph
    sourceMap2839 fusedMap2839 sourceMap2839_checked fusedMap2839_checked
    DegreeTwoThreeFiniteComparisons.comparison2839
#print axioms sourceMap2839_checked
#print axioms fusedMap2839_checked
#print axioms certified2839
def sourceMap2839swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2839swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2839swap_checked : acceptsGraphIso
    (source (graph core2839) (root 10) 4 0) DegreeTwoThreeSpectrum6323.graph sourceMap2839swap=true := by decide +kernel
theorem fusedMap2839swap_checked : acceptsGraphIso
    (fused (graph core2839) (root 10) 4 0) DegreeTwoThreeSpectrum6324.graph fusedMap2839swap=true := by decide +kernel
theorem certified2839swap : Certified (graph core2839) (root 10) 4 0 :=
  of_native_maps core2839 DegreeTwoThreeSpectrum6323.graph DegreeTwoThreeSpectrum6324.graph
    sourceMap2839swap fusedMap2839swap sourceMap2839swap_checked fusedMap2839swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2839
#print axioms sourceMap2839swap_checked
#print axioms fusedMap2839swap_checked
#print axioms certified2839swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2924 : Family 10 := level10.get ⟨1374,by decide⟩
def sourceMap2924 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2924 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2924_checked : acceptsGraphIso
    (source (graph core2924) (root 10) 0 4) DegreeTwoThreeSpectrum6719.graph sourceMap2924=true := by decide +kernel
theorem fusedMap2924_checked : acceptsGraphIso
    (fused (graph core2924) (root 10) 0 4) DegreeTwoThreeSpectrum6720.graph fusedMap2924=true := by decide +kernel
theorem certified2924 : Certified (graph core2924) (root 10) 0 4 :=
  of_native_maps core2924 DegreeTwoThreeSpectrum6719.graph DegreeTwoThreeSpectrum6720.graph
    sourceMap2924 fusedMap2924 sourceMap2924_checked fusedMap2924_checked
    DegreeTwoThreeFiniteComparisons.comparison2924
#print axioms sourceMap2924_checked
#print axioms fusedMap2924_checked
#print axioms certified2924
def sourceMap2924swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2924swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2924swap_checked : acceptsGraphIso
    (source (graph core2924) (root 10) 4 0) DegreeTwoThreeSpectrum6719.graph sourceMap2924swap=true := by decide +kernel
theorem fusedMap2924swap_checked : acceptsGraphIso
    (fused (graph core2924) (root 10) 4 0) DegreeTwoThreeSpectrum6720.graph fusedMap2924swap=true := by decide +kernel
theorem certified2924swap : Certified (graph core2924) (root 10) 4 0 :=
  of_native_maps core2924 DegreeTwoThreeSpectrum6719.graph DegreeTwoThreeSpectrum6720.graph
    sourceMap2924swap fusedMap2924swap sourceMap2924swap_checked fusedMap2924swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2924
#print axioms sourceMap2924swap_checked
#print axioms fusedMap2924swap_checked
#print axioms certified2924swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

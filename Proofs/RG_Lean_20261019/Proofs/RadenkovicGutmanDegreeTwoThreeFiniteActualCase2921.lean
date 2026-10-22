/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2921 : Family 10 := level10.get ⟨1367,by decide⟩
def sourceMap2921 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2921 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2921_checked : acceptsGraphIso
    (source (graph core2921) (root 10) 0 4) DegreeTwoThreeSpectrum6707.graph sourceMap2921=true := by decide +kernel
theorem fusedMap2921_checked : acceptsGraphIso
    (fused (graph core2921) (root 10) 0 4) DegreeTwoThreeSpectrum6708.graph fusedMap2921=true := by decide +kernel
theorem certified2921 : Certified (graph core2921) (root 10) 0 4 :=
  of_native_maps core2921 DegreeTwoThreeSpectrum6707.graph DegreeTwoThreeSpectrum6708.graph
    sourceMap2921 fusedMap2921 sourceMap2921_checked fusedMap2921_checked
    DegreeTwoThreeFiniteComparisons.comparison2921
#print axioms sourceMap2921_checked
#print axioms fusedMap2921_checked
#print axioms certified2921
def sourceMap2921swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2921swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2921swap_checked : acceptsGraphIso
    (source (graph core2921) (root 10) 4 0) DegreeTwoThreeSpectrum6707.graph sourceMap2921swap=true := by decide +kernel
theorem fusedMap2921swap_checked : acceptsGraphIso
    (fused (graph core2921) (root 10) 4 0) DegreeTwoThreeSpectrum6708.graph fusedMap2921swap=true := by decide +kernel
theorem certified2921swap : Certified (graph core2921) (root 10) 4 0 :=
  of_native_maps core2921 DegreeTwoThreeSpectrum6707.graph DegreeTwoThreeSpectrum6708.graph
    sourceMap2921swap fusedMap2921swap sourceMap2921swap_checked fusedMap2921swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2921
#print axioms sourceMap2921swap_checked
#print axioms fusedMap2921swap_checked
#print axioms certified2921swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

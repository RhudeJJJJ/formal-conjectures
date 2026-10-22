/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2916 : Family 10 := level10.get ⟨1358,by decide⟩
def sourceMap2916 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2916 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2916_checked : acceptsGraphIso
    (source (graph core2916) (root 10) 0 4) DegreeTwoThreeSpectrum6693.graph sourceMap2916=true := by decide +kernel
theorem fusedMap2916_checked : acceptsGraphIso
    (fused (graph core2916) (root 10) 0 4) DegreeTwoThreeSpectrum6694.graph fusedMap2916=true := by decide +kernel
theorem certified2916 : Certified (graph core2916) (root 10) 0 4 :=
  of_native_maps core2916 DegreeTwoThreeSpectrum6693.graph DegreeTwoThreeSpectrum6694.graph
    sourceMap2916 fusedMap2916 sourceMap2916_checked fusedMap2916_checked
    DegreeTwoThreeFiniteComparisons.comparison2916
#print axioms sourceMap2916_checked
#print axioms fusedMap2916_checked
#print axioms certified2916
def sourceMap2916swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2916swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2916swap_checked : acceptsGraphIso
    (source (graph core2916) (root 10) 4 0) DegreeTwoThreeSpectrum6693.graph sourceMap2916swap=true := by decide +kernel
theorem fusedMap2916swap_checked : acceptsGraphIso
    (fused (graph core2916) (root 10) 4 0) DegreeTwoThreeSpectrum6694.graph fusedMap2916swap=true := by decide +kernel
theorem certified2916swap : Certified (graph core2916) (root 10) 4 0 :=
  of_native_maps core2916 DegreeTwoThreeSpectrum6693.graph DegreeTwoThreeSpectrum6694.graph
    sourceMap2916swap fusedMap2916swap sourceMap2916swap_checked fusedMap2916swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2916
#print axioms sourceMap2916swap_checked
#print axioms fusedMap2916swap_checked
#print axioms certified2916swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

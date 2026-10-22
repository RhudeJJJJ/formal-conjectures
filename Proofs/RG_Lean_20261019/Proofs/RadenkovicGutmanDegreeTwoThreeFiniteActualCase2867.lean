/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2867 : Family 10 := level10.get ⟨1233,by decide⟩
def sourceMap2867 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2867 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2867_checked : acceptsGraphIso
    (source (graph core2867) (root 10) 0 4) DegreeTwoThreeSpectrum6439.graph sourceMap2867=true := by decide +kernel
theorem fusedMap2867_checked : acceptsGraphIso
    (fused (graph core2867) (root 10) 0 4) DegreeTwoThreeSpectrum6440.graph fusedMap2867=true := by decide +kernel
theorem certified2867 : Certified (graph core2867) (root 10) 0 4 :=
  of_native_maps core2867 DegreeTwoThreeSpectrum6439.graph DegreeTwoThreeSpectrum6440.graph
    sourceMap2867 fusedMap2867 sourceMap2867_checked fusedMap2867_checked
    DegreeTwoThreeFiniteComparisons.comparison2867
#print axioms sourceMap2867_checked
#print axioms fusedMap2867_checked
#print axioms certified2867
def sourceMap2867swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2867swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2867swap_checked : acceptsGraphIso
    (source (graph core2867) (root 10) 4 0) DegreeTwoThreeSpectrum6439.graph sourceMap2867swap=true := by decide +kernel
theorem fusedMap2867swap_checked : acceptsGraphIso
    (fused (graph core2867) (root 10) 4 0) DegreeTwoThreeSpectrum6440.graph fusedMap2867swap=true := by decide +kernel
theorem certified2867swap : Certified (graph core2867) (root 10) 4 0 :=
  of_native_maps core2867 DegreeTwoThreeSpectrum6439.graph DegreeTwoThreeSpectrum6440.graph
    sourceMap2867swap fusedMap2867swap sourceMap2867swap_checked fusedMap2867swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2867
#print axioms sourceMap2867swap_checked
#print axioms fusedMap2867swap_checked
#print axioms certified2867swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

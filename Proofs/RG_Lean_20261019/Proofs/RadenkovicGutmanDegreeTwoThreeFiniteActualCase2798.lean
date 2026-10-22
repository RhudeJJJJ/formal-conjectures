/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2798 : Family 10 := level10.get ⟨1074,by decide⟩
def sourceMap2798 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2798 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2798_checked : acceptsGraphIso
    (source (graph core2798) (root 10) 0 4) DegreeTwoThreeSpectrum6132.graph sourceMap2798=true := by decide +kernel
theorem fusedMap2798_checked : acceptsGraphIso
    (fused (graph core2798) (root 10) 0 4) DegreeTwoThreeSpectrum6133.graph fusedMap2798=true := by decide +kernel
theorem certified2798 : Certified (graph core2798) (root 10) 0 4 :=
  of_native_maps core2798 DegreeTwoThreeSpectrum6132.graph DegreeTwoThreeSpectrum6133.graph
    sourceMap2798 fusedMap2798 sourceMap2798_checked fusedMap2798_checked
    DegreeTwoThreeFiniteComparisons.comparison2798
#print axioms sourceMap2798_checked
#print axioms fusedMap2798_checked
#print axioms certified2798
def sourceMap2798swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2798swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2798swap_checked : acceptsGraphIso
    (source (graph core2798) (root 10) 4 0) DegreeTwoThreeSpectrum6132.graph sourceMap2798swap=true := by decide +kernel
theorem fusedMap2798swap_checked : acceptsGraphIso
    (fused (graph core2798) (root 10) 4 0) DegreeTwoThreeSpectrum6133.graph fusedMap2798swap=true := by decide +kernel
theorem certified2798swap : Certified (graph core2798) (root 10) 4 0 :=
  of_native_maps core2798 DegreeTwoThreeSpectrum6132.graph DegreeTwoThreeSpectrum6133.graph
    sourceMap2798swap fusedMap2798swap sourceMap2798swap_checked fusedMap2798swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2798
#print axioms sourceMap2798swap_checked
#print axioms fusedMap2798swap_checked
#print axioms certified2798swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

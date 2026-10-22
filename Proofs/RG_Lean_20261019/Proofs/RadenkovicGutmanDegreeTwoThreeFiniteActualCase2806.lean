/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2806 : Family 10 := level10.get ⟨1087,by decide⟩
def sourceMap2806 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2806 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2806_checked : acceptsGraphIso
    (source (graph core2806) (root 10) 0 4) DegreeTwoThreeSpectrum6156.graph sourceMap2806=true := by decide +kernel
theorem fusedMap2806_checked : acceptsGraphIso
    (fused (graph core2806) (root 10) 0 4) DegreeTwoThreeSpectrum6157.graph fusedMap2806=true := by decide +kernel
theorem certified2806 : Certified (graph core2806) (root 10) 0 4 :=
  of_native_maps core2806 DegreeTwoThreeSpectrum6156.graph DegreeTwoThreeSpectrum6157.graph
    sourceMap2806 fusedMap2806 sourceMap2806_checked fusedMap2806_checked
    DegreeTwoThreeFiniteComparisons.comparison2806
#print axioms sourceMap2806_checked
#print axioms fusedMap2806_checked
#print axioms certified2806
def sourceMap2806swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2806swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2806swap_checked : acceptsGraphIso
    (source (graph core2806) (root 10) 4 0) DegreeTwoThreeSpectrum6156.graph sourceMap2806swap=true := by decide +kernel
theorem fusedMap2806swap_checked : acceptsGraphIso
    (fused (graph core2806) (root 10) 4 0) DegreeTwoThreeSpectrum6157.graph fusedMap2806swap=true := by decide +kernel
theorem certified2806swap : Certified (graph core2806) (root 10) 4 0 :=
  of_native_maps core2806 DegreeTwoThreeSpectrum6156.graph DegreeTwoThreeSpectrum6157.graph
    sourceMap2806swap fusedMap2806swap sourceMap2806swap_checked fusedMap2806swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2806
#print axioms sourceMap2806swap_checked
#print axioms fusedMap2806swap_checked
#print axioms certified2806swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2783 : Family 10 := level10.get ⟨1029,by decide⟩
def sourceMap2783 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2783 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2783_checked : acceptsGraphIso
    (source (graph core2783) (root 10) 0 4) DegreeTwoThreeSpectrum6039.graph sourceMap2783=true := by decide +kernel
theorem fusedMap2783_checked : acceptsGraphIso
    (fused (graph core2783) (root 10) 0 4) DegreeTwoThreeSpectrum6040.graph fusedMap2783=true := by decide +kernel
theorem certified2783 : Certified (graph core2783) (root 10) 0 4 :=
  of_native_maps core2783 DegreeTwoThreeSpectrum6039.graph DegreeTwoThreeSpectrum6040.graph
    sourceMap2783 fusedMap2783 sourceMap2783_checked fusedMap2783_checked
    DegreeTwoThreeFiniteComparisons.comparison2783
#print axioms sourceMap2783_checked
#print axioms fusedMap2783_checked
#print axioms certified2783
def sourceMap2783swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2783swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2783swap_checked : acceptsGraphIso
    (source (graph core2783) (root 10) 4 0) DegreeTwoThreeSpectrum6039.graph sourceMap2783swap=true := by decide +kernel
theorem fusedMap2783swap_checked : acceptsGraphIso
    (fused (graph core2783) (root 10) 4 0) DegreeTwoThreeSpectrum6040.graph fusedMap2783swap=true := by decide +kernel
theorem certified2783swap : Certified (graph core2783) (root 10) 4 0 :=
  of_native_maps core2783 DegreeTwoThreeSpectrum6039.graph DegreeTwoThreeSpectrum6040.graph
    sourceMap2783swap fusedMap2783swap sourceMap2783swap_checked fusedMap2783swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2783
#print axioms sourceMap2783swap_checked
#print axioms fusedMap2783swap_checked
#print axioms certified2783swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

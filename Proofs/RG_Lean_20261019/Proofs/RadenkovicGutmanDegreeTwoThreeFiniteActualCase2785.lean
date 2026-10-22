/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2785 : Family 10 := level10.get ⟨1039,by decide⟩
def sourceMap2785 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2785 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2785_checked : acceptsGraphIso
    (source (graph core2785) (root 10) 0 4) DegreeTwoThreeSpectrum6060.graph sourceMap2785=true := by decide +kernel
theorem fusedMap2785_checked : acceptsGraphIso
    (fused (graph core2785) (root 10) 0 4) DegreeTwoThreeSpectrum6061.graph fusedMap2785=true := by decide +kernel
theorem certified2785 : Certified (graph core2785) (root 10) 0 4 :=
  of_native_maps core2785 DegreeTwoThreeSpectrum6060.graph DegreeTwoThreeSpectrum6061.graph
    sourceMap2785 fusedMap2785 sourceMap2785_checked fusedMap2785_checked
    DegreeTwoThreeFiniteComparisons.comparison2785
#print axioms sourceMap2785_checked
#print axioms fusedMap2785_checked
#print axioms certified2785
def sourceMap2785swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2785swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2785swap_checked : acceptsGraphIso
    (source (graph core2785) (root 10) 4 0) DegreeTwoThreeSpectrum6060.graph sourceMap2785swap=true := by decide +kernel
theorem fusedMap2785swap_checked : acceptsGraphIso
    (fused (graph core2785) (root 10) 4 0) DegreeTwoThreeSpectrum6061.graph fusedMap2785swap=true := by decide +kernel
theorem certified2785swap : Certified (graph core2785) (root 10) 4 0 :=
  of_native_maps core2785 DegreeTwoThreeSpectrum6060.graph DegreeTwoThreeSpectrum6061.graph
    sourceMap2785swap fusedMap2785swap sourceMap2785swap_checked fusedMap2785swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2785
#print axioms sourceMap2785swap_checked
#print axioms fusedMap2785swap_checked
#print axioms certified2785swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

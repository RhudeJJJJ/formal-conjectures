/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2739 : Family 10 := level10.get ⟨918,by decide⟩
def sourceMap2739 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2739 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2739_checked : acceptsGraphIso
    (source (graph core2739) (root 10) 0 4) DegreeTwoThreeSpectrum6990.graph sourceMap2739=true := by decide +kernel
theorem fusedMap2739_checked : acceptsGraphIso
    (fused (graph core2739) (root 10) 0 4) DegreeTwoThreeSpectrum5796.graph fusedMap2739=true := by decide +kernel
theorem certified2739 : Certified (graph core2739) (root 10) 0 4 :=
  of_native_maps core2739 DegreeTwoThreeSpectrum6990.graph DegreeTwoThreeSpectrum5796.graph
    sourceMap2739 fusedMap2739 sourceMap2739_checked fusedMap2739_checked
    DegreeTwoThreeFiniteComparisons.comparison2739
#print axioms sourceMap2739_checked
#print axioms fusedMap2739_checked
#print axioms certified2739
def sourceMap2739swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2739swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2739swap_checked : acceptsGraphIso
    (source (graph core2739) (root 10) 4 0) DegreeTwoThreeSpectrum6990.graph sourceMap2739swap=true := by decide +kernel
theorem fusedMap2739swap_checked : acceptsGraphIso
    (fused (graph core2739) (root 10) 4 0) DegreeTwoThreeSpectrum5796.graph fusedMap2739swap=true := by decide +kernel
theorem certified2739swap : Certified (graph core2739) (root 10) 4 0 :=
  of_native_maps core2739 DegreeTwoThreeSpectrum6990.graph DegreeTwoThreeSpectrum5796.graph
    sourceMap2739swap fusedMap2739swap sourceMap2739swap_checked fusedMap2739swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2739
#print axioms sourceMap2739swap_checked
#print axioms fusedMap2739swap_checked
#print axioms certified2739swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

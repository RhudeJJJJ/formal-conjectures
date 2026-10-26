/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3715 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap3715 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3715 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3715_checked : acceptsGraphIso
    (source (graph core3715) (root 6) 0 8) DegreeTwoThreeSpectrum5191.graph sourceMap3715=true := by decide +kernel
theorem fusedMap3715_checked : acceptsGraphIso
    (fused (graph core3715) (root 6) 0 8) DegreeTwoThreeSpectrum4967.graph fusedMap3715=true := by decide +kernel
theorem certified3715 : Certified (graph core3715) (root 6) 0 8 :=
  of_native_maps core3715 DegreeTwoThreeSpectrum5191.graph DegreeTwoThreeSpectrum4967.graph
    sourceMap3715 fusedMap3715 sourceMap3715_checked fusedMap3715_checked
    DegreeTwoThreeFiniteComparisons.comparison3715
#print axioms sourceMap3715_checked
#print axioms fusedMap3715_checked
#print axioms certified3715
def sourceMap3715swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3715swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3715swap_checked : acceptsGraphIso
    (source (graph core3715) (root 6) 8 0) DegreeTwoThreeSpectrum5191.graph sourceMap3715swap=true := by decide +kernel
theorem fusedMap3715swap_checked : acceptsGraphIso
    (fused (graph core3715) (root 6) 8 0) DegreeTwoThreeSpectrum4967.graph fusedMap3715swap=true := by decide +kernel
theorem certified3715swap : Certified (graph core3715) (root 6) 8 0 :=
  of_native_maps core3715 DegreeTwoThreeSpectrum5191.graph DegreeTwoThreeSpectrum4967.graph
    sourceMap3715swap fusedMap3715swap sourceMap3715swap_checked fusedMap3715swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3715
#print axioms sourceMap3715swap_checked
#print axioms fusedMap3715swap_checked
#print axioms certified3715swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

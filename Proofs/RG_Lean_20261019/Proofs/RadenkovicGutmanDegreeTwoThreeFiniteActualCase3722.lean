/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3722 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap3722 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3722 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3722_checked : acceptsGraphIso
    (source (graph core3722) (root 6) 0 8) DegreeTwoThreeSpectrum5679.graph sourceMap3722=true := by decide +kernel
theorem fusedMap3722_checked : acceptsGraphIso
    (fused (graph core3722) (root 6) 0 8) DegreeTwoThreeSpectrum5049.graph fusedMap3722=true := by decide +kernel
theorem certified3722 : Certified (graph core3722) (root 6) 0 8 :=
  of_native_maps core3722 DegreeTwoThreeSpectrum5679.graph DegreeTwoThreeSpectrum5049.graph
    sourceMap3722 fusedMap3722 sourceMap3722_checked fusedMap3722_checked
    DegreeTwoThreeFiniteComparisons.comparison3722
#print axioms sourceMap3722_checked
#print axioms fusedMap3722_checked
#print axioms certified3722
def sourceMap3722swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3722swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3722swap_checked : acceptsGraphIso
    (source (graph core3722) (root 6) 8 0) DegreeTwoThreeSpectrum5679.graph sourceMap3722swap=true := by decide +kernel
theorem fusedMap3722swap_checked : acceptsGraphIso
    (fused (graph core3722) (root 6) 8 0) DegreeTwoThreeSpectrum5049.graph fusedMap3722swap=true := by decide +kernel
theorem certified3722swap : Certified (graph core3722) (root 6) 8 0 :=
  of_native_maps core3722 DegreeTwoThreeSpectrum5679.graph DegreeTwoThreeSpectrum5049.graph
    sourceMap3722swap fusedMap3722swap sourceMap3722swap_checked fusedMap3722swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3722
#print axioms sourceMap3722swap_checked
#print axioms fusedMap3722swap_checked
#print axioms certified3722swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

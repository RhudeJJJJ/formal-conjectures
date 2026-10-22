/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3573 : Family 8 := level8.get ⟨123,by decide⟩
def sourceMap3573 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3573 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3573_checked : acceptsGraphIso
    (source (graph core3573) (root 8) 0 6) DegreeTwoThreeSpectrum5320.graph sourceMap3573=true := by decide +kernel
theorem fusedMap3573_checked : acceptsGraphIso
    (fused (graph core3573) (root 8) 0 6) DegreeTwoThreeSpectrum5322.graph fusedMap3573=true := by decide +kernel
theorem certified3573 : Certified (graph core3573) (root 8) 0 6 :=
  of_native_maps core3573 DegreeTwoThreeSpectrum5320.graph DegreeTwoThreeSpectrum5322.graph
    sourceMap3573 fusedMap3573 sourceMap3573_checked fusedMap3573_checked
    DegreeTwoThreeFiniteComparisons.comparison3573
#print axioms sourceMap3573_checked
#print axioms fusedMap3573_checked
#print axioms certified3573
def sourceMap3573swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3573swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3573swap_checked : acceptsGraphIso
    (source (graph core3573) (root 8) 6 0) DegreeTwoThreeSpectrum5320.graph sourceMap3573swap=true := by decide +kernel
theorem fusedMap3573swap_checked : acceptsGraphIso
    (fused (graph core3573) (root 8) 6 0) DegreeTwoThreeSpectrum5322.graph fusedMap3573swap=true := by decide +kernel
theorem certified3573swap : Certified (graph core3573) (root 8) 6 0 :=
  of_native_maps core3573 DegreeTwoThreeSpectrum5320.graph DegreeTwoThreeSpectrum5322.graph
    sourceMap3573swap fusedMap3573swap sourceMap3573swap_checked fusedMap3573swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3573
#print axioms sourceMap3573swap_checked
#print axioms fusedMap3573swap_checked
#print axioms certified3573swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1577 : Family 10 := level10.get ⟨532,by decide⟩
def sourceMap1577 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1577 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1577_checked : acceptsGraphIso
    (source (graph core1577) (root 10) 0 2) DegreeTwoThreeSpectrum3108.graph sourceMap1577=true := by decide +kernel
theorem fusedMap1577_checked : acceptsGraphIso
    (fused (graph core1577) (root 10) 0 2) DegreeTwoThreeSpectrum2471.graph fusedMap1577=true := by decide +kernel
theorem certified1577 : Certified (graph core1577) (root 10) 0 2 :=
  of_native_maps core1577 DegreeTwoThreeSpectrum3108.graph DegreeTwoThreeSpectrum2471.graph
    sourceMap1577 fusedMap1577 sourceMap1577_checked fusedMap1577_checked
    DegreeTwoThreeFiniteComparisons.comparison1577
#print axioms sourceMap1577_checked
#print axioms fusedMap1577_checked
#print axioms certified1577
def sourceMap1577swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1577swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1577swap_checked : acceptsGraphIso
    (source (graph core1577) (root 10) 2 0) DegreeTwoThreeSpectrum3108.graph sourceMap1577swap=true := by decide +kernel
theorem fusedMap1577swap_checked : acceptsGraphIso
    (fused (graph core1577) (root 10) 2 0) DegreeTwoThreeSpectrum2471.graph fusedMap1577swap=true := by decide +kernel
theorem certified1577swap : Certified (graph core1577) (root 10) 2 0 :=
  of_native_maps core1577 DegreeTwoThreeSpectrum3108.graph DegreeTwoThreeSpectrum2471.graph
    sourceMap1577swap fusedMap1577swap sourceMap1577swap_checked fusedMap1577swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1577
#print axioms sourceMap1577swap_checked
#print axioms fusedMap1577swap_checked
#print axioms certified1577swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

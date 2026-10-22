/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1755 : Family 10 := level10.get ⟨1018,by decide⟩
def sourceMap1755 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1755 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1755_checked : acceptsGraphIso
    (source (graph core1755) (root 10) 0 2) DegreeTwoThreeSpectrum3038.graph sourceMap1755=true := by decide +kernel
theorem fusedMap1755_checked : acceptsGraphIso
    (fused (graph core1755) (root 10) 0 2) DegreeTwoThreeSpectrum3040.graph fusedMap1755=true := by decide +kernel
theorem certified1755 : Certified (graph core1755) (root 10) 0 2 :=
  of_native_maps core1755 DegreeTwoThreeSpectrum3038.graph DegreeTwoThreeSpectrum3040.graph
    sourceMap1755 fusedMap1755 sourceMap1755_checked fusedMap1755_checked
    DegreeTwoThreeFiniteComparisons.comparison1755
#print axioms sourceMap1755_checked
#print axioms fusedMap1755_checked
#print axioms certified1755
def sourceMap1755swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1755swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1755swap_checked : acceptsGraphIso
    (source (graph core1755) (root 10) 2 0) DegreeTwoThreeSpectrum3038.graph sourceMap1755swap=true := by decide +kernel
theorem fusedMap1755swap_checked : acceptsGraphIso
    (fused (graph core1755) (root 10) 2 0) DegreeTwoThreeSpectrum3040.graph fusedMap1755swap=true := by decide +kernel
theorem certified1755swap : Certified (graph core1755) (root 10) 2 0 :=
  of_native_maps core1755 DegreeTwoThreeSpectrum3038.graph DegreeTwoThreeSpectrum3040.graph
    sourceMap1755swap fusedMap1755swap sourceMap1755swap_checked fusedMap1755swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1755
#print axioms sourceMap1755swap_checked
#print axioms fusedMap1755swap_checked
#print axioms certified1755swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

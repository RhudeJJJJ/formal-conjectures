/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1358 : Family 9 := level9.get ⟨500,by decide⟩
def sourceMap1358 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1358 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1358_checked : acceptsGraphIso
    (source (graph core1358) (root 9) 0 2) DegreeTwoThreeSpectrum2204.graph sourceMap1358=true := by decide +kernel
theorem fusedMap1358_checked : acceptsGraphIso
    (fused (graph core1358) (root 9) 0 2) DegreeTwoThreeSpectrum2205.graph fusedMap1358=true := by decide +kernel
theorem certified1358 : Certified (graph core1358) (root 9) 0 2 :=
  of_native_maps core1358 DegreeTwoThreeSpectrum2204.graph DegreeTwoThreeSpectrum2205.graph
    sourceMap1358 fusedMap1358 sourceMap1358_checked fusedMap1358_checked
    DegreeTwoThreeFiniteComparisons.comparison1358
#print axioms sourceMap1358_checked
#print axioms fusedMap1358_checked
#print axioms certified1358
def sourceMap1358swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1358swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1358swap_checked : acceptsGraphIso
    (source (graph core1358) (root 9) 2 0) DegreeTwoThreeSpectrum2204.graph sourceMap1358swap=true := by decide +kernel
theorem fusedMap1358swap_checked : acceptsGraphIso
    (fused (graph core1358) (root 9) 2 0) DegreeTwoThreeSpectrum2205.graph fusedMap1358swap=true := by decide +kernel
theorem certified1358swap : Certified (graph core1358) (root 9) 2 0 :=
  of_native_maps core1358 DegreeTwoThreeSpectrum2204.graph DegreeTwoThreeSpectrum2205.graph
    sourceMap1358swap fusedMap1358swap sourceMap1358swap_checked fusedMap1358swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1358
#print axioms sourceMap1358swap_checked
#print axioms fusedMap1358swap_checked
#print axioms certified1358swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

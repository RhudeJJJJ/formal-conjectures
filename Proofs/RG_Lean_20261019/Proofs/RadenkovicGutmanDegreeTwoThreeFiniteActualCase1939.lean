/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1939 : Family 10 := level10.get ⟨1462,by decide⟩
def sourceMap1939 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,7,4,5,6] (sourceLabel 10 0 2 v)
def fusedMap1939 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1939_checked : acceptsGraphIso
    (source (graph core1939) (root 10) 0 2) DegreeTwoThreeSpectrum3625.graph sourceMap1939=true := by decide +kernel
theorem fusedMap1939_checked : acceptsGraphIso
    (fused (graph core1939) (root 10) 0 2) DegreeTwoThreeSpectrum3699.graph fusedMap1939=true := by decide +kernel
theorem certified1939 : Certified (graph core1939) (root 10) 0 2 :=
  of_native_maps core1939 DegreeTwoThreeSpectrum3625.graph DegreeTwoThreeSpectrum3699.graph
    sourceMap1939 fusedMap1939 sourceMap1939_checked fusedMap1939_checked
    DegreeTwoThreeFiniteComparisons.comparison1939
#print axioms sourceMap1939_checked
#print axioms fusedMap1939_checked
#print axioms certified1939
def sourceMap1939swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,4,5,6,7] (sourceLabel 10 2 0 v)
def fusedMap1939swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1939swap_checked : acceptsGraphIso
    (source (graph core1939) (root 10) 2 0) DegreeTwoThreeSpectrum3625.graph sourceMap1939swap=true := by decide +kernel
theorem fusedMap1939swap_checked : acceptsGraphIso
    (fused (graph core1939) (root 10) 2 0) DegreeTwoThreeSpectrum3699.graph fusedMap1939swap=true := by decide +kernel
theorem certified1939swap : Certified (graph core1939) (root 10) 2 0 :=
  of_native_maps core1939 DegreeTwoThreeSpectrum3625.graph DegreeTwoThreeSpectrum3699.graph
    sourceMap1939swap fusedMap1939swap sourceMap1939swap_checked fusedMap1939swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1939
#print axioms sourceMap1939swap_checked
#print axioms fusedMap1939swap_checked
#print axioms certified1939swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

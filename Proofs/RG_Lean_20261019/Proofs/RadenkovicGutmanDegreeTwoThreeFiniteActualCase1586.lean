/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1586 : Family 10 := level10.get ⟨556,by decide⟩
def sourceMap1586 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1586 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1586_checked : acceptsGraphIso
    (source (graph core1586) (root 10) 0 2) DegreeTwoThreeSpectrum3148.graph sourceMap1586=true := by decide +kernel
theorem fusedMap1586_checked : acceptsGraphIso
    (fused (graph core1586) (root 10) 0 2) DegreeTwoThreeSpectrum2498.graph fusedMap1586=true := by decide +kernel
theorem certified1586 : Certified (graph core1586) (root 10) 0 2 :=
  of_native_maps core1586 DegreeTwoThreeSpectrum3148.graph DegreeTwoThreeSpectrum2498.graph
    sourceMap1586 fusedMap1586 sourceMap1586_checked fusedMap1586_checked
    DegreeTwoThreeFiniteComparisons.comparison1586
#print axioms sourceMap1586_checked
#print axioms fusedMap1586_checked
#print axioms certified1586
def sourceMap1586swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1586swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1586swap_checked : acceptsGraphIso
    (source (graph core1586) (root 10) 2 0) DegreeTwoThreeSpectrum3148.graph sourceMap1586swap=true := by decide +kernel
theorem fusedMap1586swap_checked : acceptsGraphIso
    (fused (graph core1586) (root 10) 2 0) DegreeTwoThreeSpectrum2498.graph fusedMap1586swap=true := by decide +kernel
theorem certified1586swap : Certified (graph core1586) (root 10) 2 0 :=
  of_native_maps core1586 DegreeTwoThreeSpectrum3148.graph DegreeTwoThreeSpectrum2498.graph
    sourceMap1586swap fusedMap1586swap sourceMap1586swap_checked fusedMap1586swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1586
#print axioms sourceMap1586swap_checked
#print axioms fusedMap1586swap_checked
#print axioms certified1586swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

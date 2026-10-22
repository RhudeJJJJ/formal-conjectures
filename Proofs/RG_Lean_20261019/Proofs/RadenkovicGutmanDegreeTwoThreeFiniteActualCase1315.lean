/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1315 : Family 9 := level9.get ⟨396,by decide⟩
def sourceMap1315 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1315 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1315_checked : acceptsGraphIso
    (source (graph core1315) (root 9) 0 2) DegreeTwoThreeSpectrum2052.graph sourceMap1315=true := by decide +kernel
theorem fusedMap1315_checked : acceptsGraphIso
    (fused (graph core1315) (root 9) 0 2) DegreeTwoThreeSpectrum2054.graph fusedMap1315=true := by decide +kernel
theorem certified1315 : Certified (graph core1315) (root 9) 0 2 :=
  of_native_maps core1315 DegreeTwoThreeSpectrum2052.graph DegreeTwoThreeSpectrum2054.graph
    sourceMap1315 fusedMap1315 sourceMap1315_checked fusedMap1315_checked
    DegreeTwoThreeFiniteComparisons.comparison1315
#print axioms sourceMap1315_checked
#print axioms fusedMap1315_checked
#print axioms certified1315
def sourceMap1315swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1315swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1315swap_checked : acceptsGraphIso
    (source (graph core1315) (root 9) 2 0) DegreeTwoThreeSpectrum2052.graph sourceMap1315swap=true := by decide +kernel
theorem fusedMap1315swap_checked : acceptsGraphIso
    (fused (graph core1315) (root 9) 2 0) DegreeTwoThreeSpectrum2054.graph fusedMap1315swap=true := by decide +kernel
theorem certified1315swap : Certified (graph core1315) (root 9) 2 0 :=
  of_native_maps core1315 DegreeTwoThreeSpectrum2052.graph DegreeTwoThreeSpectrum2054.graph
    sourceMap1315swap fusedMap1315swap sourceMap1315swap_checked fusedMap1315swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1315
#print axioms sourceMap1315swap_checked
#print axioms fusedMap1315swap_checked
#print axioms certified1315swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

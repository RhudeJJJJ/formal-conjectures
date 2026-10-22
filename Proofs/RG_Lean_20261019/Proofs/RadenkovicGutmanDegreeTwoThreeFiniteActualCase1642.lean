/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1642 : Family 10 := level10.get ⟨721,by decide⟩
def sourceMap1642 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1642 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1642_checked : acceptsGraphIso
    (source (graph core1642) (root 10) 0 2) DegreeTwoThreeSpectrum3448.graph sourceMap1642=true := by decide +kernel
theorem fusedMap1642_checked : acceptsGraphIso
    (fused (graph core1642) (root 10) 0 2) DegreeTwoThreeSpectrum2685.graph fusedMap1642=true := by decide +kernel
theorem certified1642 : Certified (graph core1642) (root 10) 0 2 :=
  of_native_maps core1642 DegreeTwoThreeSpectrum3448.graph DegreeTwoThreeSpectrum2685.graph
    sourceMap1642 fusedMap1642 sourceMap1642_checked fusedMap1642_checked
    DegreeTwoThreeFiniteComparisons.comparison1642
#print axioms sourceMap1642_checked
#print axioms fusedMap1642_checked
#print axioms certified1642
def sourceMap1642swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1642swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1642swap_checked : acceptsGraphIso
    (source (graph core1642) (root 10) 2 0) DegreeTwoThreeSpectrum3448.graph sourceMap1642swap=true := by decide +kernel
theorem fusedMap1642swap_checked : acceptsGraphIso
    (fused (graph core1642) (root 10) 2 0) DegreeTwoThreeSpectrum2685.graph fusedMap1642swap=true := by decide +kernel
theorem certified1642swap : Certified (graph core1642) (root 10) 2 0 :=
  of_native_maps core1642 DegreeTwoThreeSpectrum3448.graph DegreeTwoThreeSpectrum2685.graph
    sourceMap1642swap fusedMap1642swap sourceMap1642swap_checked fusedMap1642swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1642
#print axioms sourceMap1642swap_checked
#print axioms fusedMap1642swap_checked
#print axioms certified1642swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

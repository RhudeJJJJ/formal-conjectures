/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1776 : Family 10 := level10.get ⟨1075,by decide⟩
def sourceMap1776 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1776 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1776_checked : acceptsGraphIso
    (source (graph core1776) (root 10) 0 2) DegreeTwoThreeSpectrum3129.graph sourceMap1776=true := by decide +kernel
theorem fusedMap1776_checked : acceptsGraphIso
    (fused (graph core1776) (root 10) 0 2) DegreeTwoThreeSpectrum3131.graph fusedMap1776=true := by decide +kernel
theorem certified1776 : Certified (graph core1776) (root 10) 0 2 :=
  of_native_maps core1776 DegreeTwoThreeSpectrum3129.graph DegreeTwoThreeSpectrum3131.graph
    sourceMap1776 fusedMap1776 sourceMap1776_checked fusedMap1776_checked
    DegreeTwoThreeFiniteComparisons.comparison1776
#print axioms sourceMap1776_checked
#print axioms fusedMap1776_checked
#print axioms certified1776
def sourceMap1776swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1776swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1776swap_checked : acceptsGraphIso
    (source (graph core1776) (root 10) 2 0) DegreeTwoThreeSpectrum3129.graph sourceMap1776swap=true := by decide +kernel
theorem fusedMap1776swap_checked : acceptsGraphIso
    (fused (graph core1776) (root 10) 2 0) DegreeTwoThreeSpectrum3131.graph fusedMap1776swap=true := by decide +kernel
theorem certified1776swap : Certified (graph core1776) (root 10) 2 0 :=
  of_native_maps core1776 DegreeTwoThreeSpectrum3129.graph DegreeTwoThreeSpectrum3131.graph
    sourceMap1776swap fusedMap1776swap sourceMap1776swap_checked fusedMap1776swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1776
#print axioms sourceMap1776swap_checked
#print axioms fusedMap1776swap_checked
#print axioms certified1776swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

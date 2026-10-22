/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1575 : Family 10 := level10.get ⟨528,by decide⟩
def sourceMap1575 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1575 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1575_checked : acceptsGraphIso
    (source (graph core1575) (root 10) 0 2) DegreeTwoThreeSpectrum3104.graph sourceMap1575=true := by decide +kernel
theorem fusedMap1575_checked : acceptsGraphIso
    (fused (graph core1575) (root 10) 0 2) DegreeTwoThreeSpectrum2465.graph fusedMap1575=true := by decide +kernel
theorem certified1575 : Certified (graph core1575) (root 10) 0 2 :=
  of_native_maps core1575 DegreeTwoThreeSpectrum3104.graph DegreeTwoThreeSpectrum2465.graph
    sourceMap1575 fusedMap1575 sourceMap1575_checked fusedMap1575_checked
    DegreeTwoThreeFiniteComparisons.comparison1575
#print axioms sourceMap1575_checked
#print axioms fusedMap1575_checked
#print axioms certified1575
def sourceMap1575swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1575swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1575swap_checked : acceptsGraphIso
    (source (graph core1575) (root 10) 2 0) DegreeTwoThreeSpectrum3104.graph sourceMap1575swap=true := by decide +kernel
theorem fusedMap1575swap_checked : acceptsGraphIso
    (fused (graph core1575) (root 10) 2 0) DegreeTwoThreeSpectrum2465.graph fusedMap1575swap=true := by decide +kernel
theorem certified1575swap : Certified (graph core1575) (root 10) 2 0 :=
  of_native_maps core1575 DegreeTwoThreeSpectrum3104.graph DegreeTwoThreeSpectrum2465.graph
    sourceMap1575swap fusedMap1575swap sourceMap1575swap_checked fusedMap1575swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1575
#print axioms sourceMap1575swap_checked
#print axioms fusedMap1575swap_checked
#print axioms certified1575swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

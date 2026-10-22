/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1691 : Family 10 := level10.get ⟨860,by decide⟩
def sourceMap1691 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1691 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1691_checked : acceptsGraphIso
    (source (graph core1691) (root 10) 0 2) DegreeTwoThreeSpectrum3680.graph sourceMap1691=true := by decide +kernel
theorem fusedMap1691_checked : acceptsGraphIso
    (fused (graph core1691) (root 10) 0 2) DegreeTwoThreeSpectrum2847.graph fusedMap1691=true := by decide +kernel
theorem certified1691 : Certified (graph core1691) (root 10) 0 2 :=
  of_native_maps core1691 DegreeTwoThreeSpectrum3680.graph DegreeTwoThreeSpectrum2847.graph
    sourceMap1691 fusedMap1691 sourceMap1691_checked fusedMap1691_checked
    DegreeTwoThreeFiniteComparisons.comparison1691
#print axioms sourceMap1691_checked
#print axioms fusedMap1691_checked
#print axioms certified1691
def sourceMap1691swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1691swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1691swap_checked : acceptsGraphIso
    (source (graph core1691) (root 10) 2 0) DegreeTwoThreeSpectrum3680.graph sourceMap1691swap=true := by decide +kernel
theorem fusedMap1691swap_checked : acceptsGraphIso
    (fused (graph core1691) (root 10) 2 0) DegreeTwoThreeSpectrum2847.graph fusedMap1691swap=true := by decide +kernel
theorem certified1691swap : Certified (graph core1691) (root 10) 2 0 :=
  of_native_maps core1691 DegreeTwoThreeSpectrum3680.graph DegreeTwoThreeSpectrum2847.graph
    sourceMap1691swap fusedMap1691swap sourceMap1691swap_checked fusedMap1691swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1691
#print axioms sourceMap1691swap_checked
#print axioms fusedMap1691swap_checked
#print axioms certified1691swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

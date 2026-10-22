/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1537 : Family 10 := level10.get ⟨414,by decide⟩
def sourceMap1537 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1537 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1537_checked : acceptsGraphIso
    (source (graph core1537) (root 10) 0 2) DegreeTwoThreeSpectrum2851.graph sourceMap1537=true := by decide +kernel
theorem fusedMap1537_checked : acceptsGraphIso
    (fused (graph core1537) (root 10) 0 2) DegreeTwoThreeSpectrum2927.graph fusedMap1537=true := by decide +kernel
theorem certified1537 : Certified (graph core1537) (root 10) 0 2 :=
  of_native_maps core1537 DegreeTwoThreeSpectrum2851.graph DegreeTwoThreeSpectrum2927.graph
    sourceMap1537 fusedMap1537 sourceMap1537_checked fusedMap1537_checked
    DegreeTwoThreeFiniteComparisons.comparison1537
#print axioms sourceMap1537_checked
#print axioms fusedMap1537_checked
#print axioms certified1537
def sourceMap1537swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1537swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1537swap_checked : acceptsGraphIso
    (source (graph core1537) (root 10) 2 0) DegreeTwoThreeSpectrum2851.graph sourceMap1537swap=true := by decide +kernel
theorem fusedMap1537swap_checked : acceptsGraphIso
    (fused (graph core1537) (root 10) 2 0) DegreeTwoThreeSpectrum2927.graph fusedMap1537swap=true := by decide +kernel
theorem certified1537swap : Certified (graph core1537) (root 10) 2 0 :=
  of_native_maps core1537 DegreeTwoThreeSpectrum2851.graph DegreeTwoThreeSpectrum2927.graph
    sourceMap1537swap fusedMap1537swap sourceMap1537swap_checked fusedMap1537swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1537
#print axioms sourceMap1537swap_checked
#print axioms fusedMap1537swap_checked
#print axioms certified1537swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

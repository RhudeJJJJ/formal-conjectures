/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1785 : Family 10 := level10.get ⟨1097,by decide⟩
def sourceMap1785 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1785 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1785_checked : acceptsGraphIso
    (source (graph core1785) (root 10) 0 2) DegreeTwoThreeSpectrum3161.graph sourceMap1785=true := by decide +kernel
theorem fusedMap1785_checked : acceptsGraphIso
    (fused (graph core1785) (root 10) 0 2) DegreeTwoThreeSpectrum3162.graph fusedMap1785=true := by decide +kernel
theorem certified1785 : Certified (graph core1785) (root 10) 0 2 :=
  of_native_maps core1785 DegreeTwoThreeSpectrum3161.graph DegreeTwoThreeSpectrum3162.graph
    sourceMap1785 fusedMap1785 sourceMap1785_checked fusedMap1785_checked
    DegreeTwoThreeFiniteComparisons.comparison1785
#print axioms sourceMap1785_checked
#print axioms fusedMap1785_checked
#print axioms certified1785
def sourceMap1785swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1785swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1785swap_checked : acceptsGraphIso
    (source (graph core1785) (root 10) 2 0) DegreeTwoThreeSpectrum3161.graph sourceMap1785swap=true := by decide +kernel
theorem fusedMap1785swap_checked : acceptsGraphIso
    (fused (graph core1785) (root 10) 2 0) DegreeTwoThreeSpectrum3162.graph fusedMap1785swap=true := by decide +kernel
theorem certified1785swap : Certified (graph core1785) (root 10) 2 0 :=
  of_native_maps core1785 DegreeTwoThreeSpectrum3161.graph DegreeTwoThreeSpectrum3162.graph
    sourceMap1785swap fusedMap1785swap sourceMap1785swap_checked fusedMap1785swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1785
#print axioms sourceMap1785swap_checked
#print axioms fusedMap1785swap_checked
#print axioms certified1785swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

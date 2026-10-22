/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1872 : Family 10 := level10.get ⟨1310,by decide⟩
def sourceMap1872 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1872 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1872_checked : acceptsGraphIso
    (source (graph core1872) (root 10) 0 2) DegreeTwoThreeSpectrum3477.graph sourceMap1872=true := by decide +kernel
theorem fusedMap1872_checked : acceptsGraphIso
    (fused (graph core1872) (root 10) 0 2) DegreeTwoThreeSpectrum3478.graph fusedMap1872=true := by decide +kernel
theorem certified1872 : Certified (graph core1872) (root 10) 0 2 :=
  of_native_maps core1872 DegreeTwoThreeSpectrum3477.graph DegreeTwoThreeSpectrum3478.graph
    sourceMap1872 fusedMap1872 sourceMap1872_checked fusedMap1872_checked
    DegreeTwoThreeFiniteComparisons.comparison1872
#print axioms sourceMap1872_checked
#print axioms fusedMap1872_checked
#print axioms certified1872
def sourceMap1872swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1872swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1872swap_checked : acceptsGraphIso
    (source (graph core1872) (root 10) 2 0) DegreeTwoThreeSpectrum3477.graph sourceMap1872swap=true := by decide +kernel
theorem fusedMap1872swap_checked : acceptsGraphIso
    (fused (graph core1872) (root 10) 2 0) DegreeTwoThreeSpectrum3478.graph fusedMap1872swap=true := by decide +kernel
theorem certified1872swap : Certified (graph core1872) (root 10) 2 0 :=
  of_native_maps core1872 DegreeTwoThreeSpectrum3477.graph DegreeTwoThreeSpectrum3478.graph
    sourceMap1872swap fusedMap1872swap sourceMap1872swap_checked fusedMap1872swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1872
#print axioms sourceMap1872swap_checked
#print axioms fusedMap1872swap_checked
#print axioms certified1872swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

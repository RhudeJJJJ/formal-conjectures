/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1353 : Family 9 := level9.get ⟨488,by decide⟩
def sourceMap1353 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1353 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1353_checked : acceptsGraphIso
    (source (graph core1353) (root 9) 0 2) DegreeTwoThreeSpectrum2184.graph sourceMap1353=true := by decide +kernel
theorem fusedMap1353_checked : acceptsGraphIso
    (fused (graph core1353) (root 9) 0 2) DegreeTwoThreeSpectrum2186.graph fusedMap1353=true := by decide +kernel
theorem certified1353 : Certified (graph core1353) (root 9) 0 2 :=
  of_native_maps core1353 DegreeTwoThreeSpectrum2184.graph DegreeTwoThreeSpectrum2186.graph
    sourceMap1353 fusedMap1353 sourceMap1353_checked fusedMap1353_checked
    DegreeTwoThreeFiniteComparisons.comparison1353
#print axioms sourceMap1353_checked
#print axioms fusedMap1353_checked
#print axioms certified1353
def sourceMap1353swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1353swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1353swap_checked : acceptsGraphIso
    (source (graph core1353) (root 9) 2 0) DegreeTwoThreeSpectrum2184.graph sourceMap1353swap=true := by decide +kernel
theorem fusedMap1353swap_checked : acceptsGraphIso
    (fused (graph core1353) (root 9) 2 0) DegreeTwoThreeSpectrum2186.graph fusedMap1353swap=true := by decide +kernel
theorem certified1353swap : Certified (graph core1353) (root 9) 2 0 :=
  of_native_maps core1353 DegreeTwoThreeSpectrum2184.graph DegreeTwoThreeSpectrum2186.graph
    sourceMap1353swap fusedMap1353swap sourceMap1353swap_checked fusedMap1353swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1353
#print axioms sourceMap1353swap_checked
#print axioms fusedMap1353swap_checked
#print axioms certified1353swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

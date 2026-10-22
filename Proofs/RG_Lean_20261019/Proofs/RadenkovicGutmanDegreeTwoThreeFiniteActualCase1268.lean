/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1268 : Family 9 := level9.get ⟨272,by decide⟩
def sourceMap1268 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1268 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1268_checked : acceptsGraphIso
    (source (graph core1268) (root 9) 0 2) DegreeTwoThreeSpectrum2222.graph sourceMap1268=true := by decide +kernel
theorem fusedMap1268_checked : acceptsGraphIso
    (fused (graph core1268) (root 9) 0 2) DegreeTwoThreeSpectrum1881.graph fusedMap1268=true := by decide +kernel
theorem certified1268 : Certified (graph core1268) (root 9) 0 2 :=
  of_native_maps core1268 DegreeTwoThreeSpectrum2222.graph DegreeTwoThreeSpectrum1881.graph
    sourceMap1268 fusedMap1268 sourceMap1268_checked fusedMap1268_checked
    DegreeTwoThreeFiniteComparisons.comparison1268
#print axioms sourceMap1268_checked
#print axioms fusedMap1268_checked
#print axioms certified1268
def sourceMap1268swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1268swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1268swap_checked : acceptsGraphIso
    (source (graph core1268) (root 9) 2 0) DegreeTwoThreeSpectrum2222.graph sourceMap1268swap=true := by decide +kernel
theorem fusedMap1268swap_checked : acceptsGraphIso
    (fused (graph core1268) (root 9) 2 0) DegreeTwoThreeSpectrum1881.graph fusedMap1268swap=true := by decide +kernel
theorem certified1268swap : Certified (graph core1268) (root 9) 2 0 :=
  of_native_maps core1268 DegreeTwoThreeSpectrum2222.graph DegreeTwoThreeSpectrum1881.graph
    sourceMap1268swap fusedMap1268swap sourceMap1268swap_checked fusedMap1268swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1268
#print axioms sourceMap1268swap_checked
#print axioms fusedMap1268swap_checked
#print axioms certified1268swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1941 : Family 10 := level10.get ⟨1466,by decide⟩
def sourceMap1941 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1941 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1941_checked : acceptsGraphIso
    (source (graph core1941) (root 10) 0 2) DegreeTwoThreeSpectrum3710.graph sourceMap1941=true := by decide +kernel
theorem fusedMap1941_checked : acceptsGraphIso
    (fused (graph core1941) (root 10) 0 2) DegreeTwoThreeSpectrum3707.graph fusedMap1941=true := by decide +kernel
theorem certified1941 : Certified (graph core1941) (root 10) 0 2 :=
  of_native_maps core1941 DegreeTwoThreeSpectrum3710.graph DegreeTwoThreeSpectrum3707.graph
    sourceMap1941 fusedMap1941 sourceMap1941_checked fusedMap1941_checked
    DegreeTwoThreeFiniteComparisons.comparison1941
#print axioms sourceMap1941_checked
#print axioms fusedMap1941_checked
#print axioms certified1941
def sourceMap1941swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1941swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1941swap_checked : acceptsGraphIso
    (source (graph core1941) (root 10) 2 0) DegreeTwoThreeSpectrum3710.graph sourceMap1941swap=true := by decide +kernel
theorem fusedMap1941swap_checked : acceptsGraphIso
    (fused (graph core1941) (root 10) 2 0) DegreeTwoThreeSpectrum3707.graph fusedMap1941swap=true := by decide +kernel
theorem certified1941swap : Certified (graph core1941) (root 10) 2 0 :=
  of_native_maps core1941 DegreeTwoThreeSpectrum3710.graph DegreeTwoThreeSpectrum3707.graph
    sourceMap1941swap fusedMap1941swap sourceMap1941swap_checked fusedMap1941swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1941
#print axioms sourceMap1941swap_checked
#print axioms fusedMap1941swap_checked
#print axioms certified1941swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

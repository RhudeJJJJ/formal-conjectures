/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1257 : Family 9 := level9.get ⟨242,by decide⟩
def sourceMap1257 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,11,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1257 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1257_checked : acceptsGraphIso
    (source (graph core1257) (root 9) 0 2) DegreeTwoThreeSpectrum2172.graph sourceMap1257=true := by decide +kernel
theorem fusedMap1257_checked : acceptsGraphIso
    (fused (graph core1257) (root 9) 0 2) DegreeTwoThreeSpectrum1844.graph fusedMap1257=true := by decide +kernel
theorem certified1257 : Certified (graph core1257) (root 9) 0 2 :=
  of_native_maps core1257 DegreeTwoThreeSpectrum2172.graph DegreeTwoThreeSpectrum1844.graph
    sourceMap1257 fusedMap1257 sourceMap1257_checked fusedMap1257_checked
    DegreeTwoThreeFiniteComparisons.comparison1257
#print axioms sourceMap1257_checked
#print axioms fusedMap1257_checked
#print axioms certified1257
def sourceMap1257swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,7,8,9,11] (sourceLabel 9 2 0 v)
def fusedMap1257swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1257swap_checked : acceptsGraphIso
    (source (graph core1257) (root 9) 2 0) DegreeTwoThreeSpectrum2172.graph sourceMap1257swap=true := by decide +kernel
theorem fusedMap1257swap_checked : acceptsGraphIso
    (fused (graph core1257) (root 9) 2 0) DegreeTwoThreeSpectrum1844.graph fusedMap1257swap=true := by decide +kernel
theorem certified1257swap : Certified (graph core1257) (root 9) 2 0 :=
  of_native_maps core1257 DegreeTwoThreeSpectrum2172.graph DegreeTwoThreeSpectrum1844.graph
    sourceMap1257swap fusedMap1257swap sourceMap1257swap_checked fusedMap1257swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1257
#print axioms sourceMap1257swap_checked
#print axioms fusedMap1257swap_checked
#print axioms certified1257swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

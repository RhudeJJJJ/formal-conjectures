/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1253 : Family 9 := level9.get ⟨230,by decide⟩
def sourceMap1253 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1253 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1253_checked : acceptsGraphIso
    (source (graph core1253) (root 9) 0 2) DegreeTwoThreeSpectrum2154.graph sourceMap1253=true := by decide +kernel
theorem fusedMap1253_checked : acceptsGraphIso
    (fused (graph core1253) (root 9) 0 2) DegreeTwoThreeSpectrum1833.graph fusedMap1253=true := by decide +kernel
theorem certified1253 : Certified (graph core1253) (root 9) 0 2 :=
  of_native_maps core1253 DegreeTwoThreeSpectrum2154.graph DegreeTwoThreeSpectrum1833.graph
    sourceMap1253 fusedMap1253 sourceMap1253_checked fusedMap1253_checked
    DegreeTwoThreeFiniteComparisons.comparison1253
#print axioms sourceMap1253_checked
#print axioms fusedMap1253_checked
#print axioms certified1253
def sourceMap1253swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1253swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1253swap_checked : acceptsGraphIso
    (source (graph core1253) (root 9) 2 0) DegreeTwoThreeSpectrum2154.graph sourceMap1253swap=true := by decide +kernel
theorem fusedMap1253swap_checked : acceptsGraphIso
    (fused (graph core1253) (root 9) 2 0) DegreeTwoThreeSpectrum1833.graph fusedMap1253swap=true := by decide +kernel
theorem certified1253swap : Certified (graph core1253) (root 9) 2 0 :=
  of_native_maps core1253 DegreeTwoThreeSpectrum2154.graph DegreeTwoThreeSpectrum1833.graph
    sourceMap1253swap fusedMap1253swap sourceMap1253swap_checked fusedMap1253swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1253
#print axioms sourceMap1253swap_checked
#print axioms fusedMap1253swap_checked
#print axioms certified1253swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

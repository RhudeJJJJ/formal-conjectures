/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3466 : Family 9 := level9.get ⟨654,by decide⟩
def sourceMap3466 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3466 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3466_checked : acceptsGraphIso
    (source (graph core3466) (root 9) 0 5) DegreeTwoThreeSpectrum6601.graph sourceMap3466=true := by decide +kernel
theorem fusedMap3466_checked : acceptsGraphIso
    (fused (graph core3466) (root 9) 0 5) DegreeTwoThreeSpectrum6602.graph fusedMap3466=true := by decide +kernel
theorem certified3466 : Certified (graph core3466) (root 9) 0 5 :=
  of_native_maps core3466 DegreeTwoThreeSpectrum6601.graph DegreeTwoThreeSpectrum6602.graph
    sourceMap3466 fusedMap3466 sourceMap3466_checked fusedMap3466_checked
    DegreeTwoThreeFiniteComparisons.comparison3466
#print axioms sourceMap3466_checked
#print axioms fusedMap3466_checked
#print axioms certified3466
def sourceMap3466swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3466swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3466swap_checked : acceptsGraphIso
    (source (graph core3466) (root 9) 5 0) DegreeTwoThreeSpectrum6601.graph sourceMap3466swap=true := by decide +kernel
theorem fusedMap3466swap_checked : acceptsGraphIso
    (fused (graph core3466) (root 9) 5 0) DegreeTwoThreeSpectrum6602.graph fusedMap3466swap=true := by decide +kernel
theorem certified3466swap : Certified (graph core3466) (root 9) 5 0 :=
  of_native_maps core3466 DegreeTwoThreeSpectrum6601.graph DegreeTwoThreeSpectrum6602.graph
    sourceMap3466swap fusedMap3466swap sourceMap3466swap_checked fusedMap3466swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3466
#print axioms sourceMap3466swap_checked
#print axioms fusedMap3466swap_checked
#print axioms certified3466swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

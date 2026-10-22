/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3137 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap3137 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3137 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3137_checked : acceptsGraphIso
    (source (graph core3137) (root 7) 0 5) DegreeTwoThreeSpectrum3008.graph sourceMap3137=true := by decide +kernel
theorem fusedMap3137_checked : acceptsGraphIso
    (fused (graph core3137) (root 7) 0 5) DegreeTwoThreeSpectrum2437.graph fusedMap3137=true := by decide +kernel
theorem certified3137 : Certified (graph core3137) (root 7) 0 5 :=
  of_native_maps core3137 DegreeTwoThreeSpectrum3008.graph DegreeTwoThreeSpectrum2437.graph
    sourceMap3137 fusedMap3137 sourceMap3137_checked fusedMap3137_checked
    DegreeTwoThreeFiniteComparisons.comparison3137
#print axioms sourceMap3137_checked
#print axioms fusedMap3137_checked
#print axioms certified3137
def sourceMap3137swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,10] (sourceLabel 7 5 0 v)
def fusedMap3137swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3137swap_checked : acceptsGraphIso
    (source (graph core3137) (root 7) 5 0) DegreeTwoThreeSpectrum3008.graph sourceMap3137swap=true := by decide +kernel
theorem fusedMap3137swap_checked : acceptsGraphIso
    (fused (graph core3137) (root 7) 5 0) DegreeTwoThreeSpectrum2437.graph fusedMap3137swap=true := by decide +kernel
theorem certified3137swap : Certified (graph core3137) (root 7) 5 0 :=
  of_native_maps core3137 DegreeTwoThreeSpectrum3008.graph DegreeTwoThreeSpectrum2437.graph
    sourceMap3137swap fusedMap3137swap sourceMap3137swap_checked fusedMap3137swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3137
#print axioms sourceMap3137swap_checked
#print axioms fusedMap3137swap_checked
#print axioms certified3137swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

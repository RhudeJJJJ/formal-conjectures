/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3241 : Family 9 := level9.get ⟨37,by decide⟩
def sourceMap3241 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3241 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 0 5 v)
theorem sourceMap3241_checked : acceptsGraphIso
    (source (graph core3241) (root 9) 0 5) DegreeTwoThreeSpectrum5121.graph sourceMap3241=true := by decide +kernel
theorem fusedMap3241_checked : acceptsGraphIso
    (fused (graph core3241) (root 9) 0 5) DegreeTwoThreeSpectrum5123.graph fusedMap3241=true := by decide +kernel
theorem certified3241 : Certified (graph core3241) (root 9) 0 5 :=
  of_native_maps core3241 DegreeTwoThreeSpectrum5121.graph DegreeTwoThreeSpectrum5123.graph
    sourceMap3241 fusedMap3241 sourceMap3241_checked fusedMap3241_checked
    DegreeTwoThreeFiniteComparisons.comparison3241
#print axioms sourceMap3241_checked
#print axioms fusedMap3241_checked
#print axioms certified3241
def sourceMap3241swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3241swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 5 0 v)
theorem sourceMap3241swap_checked : acceptsGraphIso
    (source (graph core3241) (root 9) 5 0) DegreeTwoThreeSpectrum5121.graph sourceMap3241swap=true := by decide +kernel
theorem fusedMap3241swap_checked : acceptsGraphIso
    (fused (graph core3241) (root 9) 5 0) DegreeTwoThreeSpectrum5123.graph fusedMap3241swap=true := by decide +kernel
theorem certified3241swap : Certified (graph core3241) (root 9) 5 0 :=
  of_native_maps core3241 DegreeTwoThreeSpectrum5121.graph DegreeTwoThreeSpectrum5123.graph
    sourceMap3241swap fusedMap3241swap sourceMap3241swap_checked fusedMap3241swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3241
#print axioms sourceMap3241swap_checked
#print axioms fusedMap3241swap_checked
#print axioms certified3241swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

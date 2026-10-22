/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3104 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap3104 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3104 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3104_checked : acceptsGraphIso
    (source (graph core3104) (root 7) 0 5) DegreeTwoThreeSpectrum2340.graph sourceMap3104=true := by decide +kernel
theorem fusedMap3104_checked : acceptsGraphIso
    (fused (graph core3104) (root 7) 0 5) DegreeTwoThreeSpectrum2342.graph fusedMap3104=true := by decide +kernel
theorem certified3104 : Certified (graph core3104) (root 7) 0 5 :=
  of_native_maps core3104 DegreeTwoThreeSpectrum2340.graph DegreeTwoThreeSpectrum2342.graph
    sourceMap3104 fusedMap3104 sourceMap3104_checked fusedMap3104_checked
    DegreeTwoThreeFiniteComparisons.comparison3104
#print axioms sourceMap3104_checked
#print axioms fusedMap3104_checked
#print axioms certified3104
def sourceMap3104swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,14,8] (sourceLabel 7 5 0 v)
def fusedMap3104swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3104swap_checked : acceptsGraphIso
    (source (graph core3104) (root 7) 5 0) DegreeTwoThreeSpectrum2340.graph sourceMap3104swap=true := by decide +kernel
theorem fusedMap3104swap_checked : acceptsGraphIso
    (fused (graph core3104) (root 7) 5 0) DegreeTwoThreeSpectrum2342.graph fusedMap3104swap=true := by decide +kernel
theorem certified3104swap : Certified (graph core3104) (root 7) 5 0 :=
  of_native_maps core3104 DegreeTwoThreeSpectrum2340.graph DegreeTwoThreeSpectrum2342.graph
    sourceMap3104swap fusedMap3104swap sourceMap3104swap_checked fusedMap3104swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3104
#print axioms sourceMap3104swap_checked
#print axioms fusedMap3104swap_checked
#print axioms certified3104swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3308 : Family 9 := level9.get ⟨261,by decide⟩
def sourceMap3308 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3308 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3308_checked : acceptsGraphIso
    (source (graph core3308) (root 9) 0 5) DegreeTwoThreeSpectrum5699.graph sourceMap3308=true := by decide +kernel
theorem fusedMap3308_checked : acceptsGraphIso
    (fused (graph core3308) (root 9) 0 5) DegreeTwoThreeSpectrum5700.graph fusedMap3308=true := by decide +kernel
theorem certified3308 : Certified (graph core3308) (root 9) 0 5 :=
  of_native_maps core3308 DegreeTwoThreeSpectrum5699.graph DegreeTwoThreeSpectrum5700.graph
    sourceMap3308 fusedMap3308 sourceMap3308_checked fusedMap3308_checked
    DegreeTwoThreeFiniteComparisons.comparison3308
#print axioms sourceMap3308_checked
#print axioms fusedMap3308_checked
#print axioms certified3308
def sourceMap3308swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3308swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3308swap_checked : acceptsGraphIso
    (source (graph core3308) (root 9) 5 0) DegreeTwoThreeSpectrum5699.graph sourceMap3308swap=true := by decide +kernel
theorem fusedMap3308swap_checked : acceptsGraphIso
    (fused (graph core3308) (root 9) 5 0) DegreeTwoThreeSpectrum5700.graph fusedMap3308swap=true := by decide +kernel
theorem certified3308swap : Certified (graph core3308) (root 9) 5 0 :=
  of_native_maps core3308 DegreeTwoThreeSpectrum5699.graph DegreeTwoThreeSpectrum5700.graph
    sourceMap3308swap fusedMap3308swap sourceMap3308swap_checked fusedMap3308swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3308
#print axioms sourceMap3308swap_checked
#print axioms fusedMap3308swap_checked
#print axioms certified3308swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

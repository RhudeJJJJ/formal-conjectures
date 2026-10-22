/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3954 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap3954 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3954 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3954_checked : acceptsGraphIso
    (source (graph core3954) (root 7) 1 5) DegreeTwoThreeSpectrum4141.graph sourceMap3954=true := by decide +kernel
theorem fusedMap3954_checked : acceptsGraphIso
    (fused (graph core3954) (root 7) 1 5) DegreeTwoThreeSpectrum3879.graph fusedMap3954=true := by decide +kernel
theorem certified3954 : Certified (graph core3954) (root 7) 1 5 :=
  of_native_maps core3954 DegreeTwoThreeSpectrum4141.graph DegreeTwoThreeSpectrum3879.graph
    sourceMap3954 fusedMap3954 sourceMap3954_checked fusedMap3954_checked
    DegreeTwoThreeFiniteComparisons.comparison3954
#print axioms sourceMap3954_checked
#print axioms fusedMap3954_checked
#print axioms certified3954
def sourceMap3954swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,15,7,8] (sourceLabel 7 5 1 v)
def fusedMap3954swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3954swap_checked : acceptsGraphIso
    (source (graph core3954) (root 7) 5 1) DegreeTwoThreeSpectrum4141.graph sourceMap3954swap=true := by decide +kernel
theorem fusedMap3954swap_checked : acceptsGraphIso
    (fused (graph core3954) (root 7) 5 1) DegreeTwoThreeSpectrum3879.graph fusedMap3954swap=true := by decide +kernel
theorem certified3954swap : Certified (graph core3954) (root 7) 5 1 :=
  of_native_maps core3954 DegreeTwoThreeSpectrum4141.graph DegreeTwoThreeSpectrum3879.graph
    sourceMap3954swap fusedMap3954swap sourceMap3954swap_checked fusedMap3954swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3954
#print axioms sourceMap3954swap_checked
#print axioms fusedMap3954swap_checked
#print axioms certified3954swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3659 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap3659 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3659 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3659_checked : acceptsGraphIso
    (source (graph core3659) (root 6) 0 7) DegreeTwoThreeSpectrum4187.graph sourceMap3659=true := by decide +kernel
theorem fusedMap3659_checked : acceptsGraphIso
    (fused (graph core3659) (root 6) 0 7) DegreeTwoThreeSpectrum3893.graph fusedMap3659=true := by decide +kernel
theorem certified3659 : Certified (graph core3659) (root 6) 0 7 :=
  of_native_maps core3659 DegreeTwoThreeSpectrum4187.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap3659 fusedMap3659 sourceMap3659_checked fusedMap3659_checked
    DegreeTwoThreeFiniteComparisons.comparison3659
#print axioms sourceMap3659_checked
#print axioms fusedMap3659_checked
#print axioms certified3659
def sourceMap3659swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,10] (sourceLabel 6 7 0 v)
def fusedMap3659swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3659swap_checked : acceptsGraphIso
    (source (graph core3659) (root 6) 7 0) DegreeTwoThreeSpectrum4187.graph sourceMap3659swap=true := by decide +kernel
theorem fusedMap3659swap_checked : acceptsGraphIso
    (fused (graph core3659) (root 6) 7 0) DegreeTwoThreeSpectrum3893.graph fusedMap3659swap=true := by decide +kernel
theorem certified3659swap : Certified (graph core3659) (root 6) 7 0 :=
  of_native_maps core3659 DegreeTwoThreeSpectrum4187.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap3659swap fusedMap3659swap sourceMap3659swap_checked fusedMap3659swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3659
#print axioms sourceMap3659swap_checked
#print axioms fusedMap3659swap_checked
#print axioms certified3659swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

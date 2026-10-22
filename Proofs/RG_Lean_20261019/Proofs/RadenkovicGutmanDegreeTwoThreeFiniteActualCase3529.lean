/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3529 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap3529 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3529 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3529_checked : acceptsGraphIso
    (source (graph core3529) (root 7) 0 6) DegreeTwoThreeSpectrum4407.graph sourceMap3529=true := by decide +kernel
theorem fusedMap3529_checked : acceptsGraphIso
    (fused (graph core3529) (root 7) 0 6) DegreeTwoThreeSpectrum3983.graph fusedMap3529=true := by decide +kernel
theorem certified3529 : Certified (graph core3529) (root 7) 0 6 :=
  of_native_maps core3529 DegreeTwoThreeSpectrum4407.graph DegreeTwoThreeSpectrum3983.graph
    sourceMap3529 fusedMap3529 sourceMap3529_checked fusedMap3529_checked
    DegreeTwoThreeFiniteComparisons.comparison3529
#print axioms sourceMap3529_checked
#print axioms fusedMap3529_checked
#print axioms certified3529
def sourceMap3529swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3529swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3529swap_checked : acceptsGraphIso
    (source (graph core3529) (root 7) 6 0) DegreeTwoThreeSpectrum4407.graph sourceMap3529swap=true := by decide +kernel
theorem fusedMap3529swap_checked : acceptsGraphIso
    (fused (graph core3529) (root 7) 6 0) DegreeTwoThreeSpectrum3983.graph fusedMap3529swap=true := by decide +kernel
theorem certified3529swap : Certified (graph core3529) (root 7) 6 0 :=
  of_native_maps core3529 DegreeTwoThreeSpectrum4407.graph DegreeTwoThreeSpectrum3983.graph
    sourceMap3529swap fusedMap3529swap sourceMap3529swap_checked fusedMap3529swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3529
#print axioms sourceMap3529swap_checked
#print axioms fusedMap3529swap_checked
#print axioms certified3529swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3536 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap3536 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3536 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3536_checked : acceptsGraphIso
    (source (graph core3536) (root 7) 0 6) DegreeTwoThreeSpectrum4174.graph sourceMap3536=true := by decide +kernel
theorem fusedMap3536_checked : acceptsGraphIso
    (fused (graph core3536) (root 7) 0 6) DegreeTwoThreeSpectrum4176.graph fusedMap3536=true := by decide +kernel
theorem certified3536 : Certified (graph core3536) (root 7) 0 6 :=
  of_native_maps core3536 DegreeTwoThreeSpectrum4174.graph DegreeTwoThreeSpectrum4176.graph
    sourceMap3536 fusedMap3536 sourceMap3536_checked fusedMap3536_checked
    DegreeTwoThreeFiniteComparisons.comparison3536
#print axioms sourceMap3536_checked
#print axioms fusedMap3536_checked
#print axioms certified3536
def sourceMap3536swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3536swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3536swap_checked : acceptsGraphIso
    (source (graph core3536) (root 7) 6 0) DegreeTwoThreeSpectrum4174.graph sourceMap3536swap=true := by decide +kernel
theorem fusedMap3536swap_checked : acceptsGraphIso
    (fused (graph core3536) (root 7) 6 0) DegreeTwoThreeSpectrum4176.graph fusedMap3536swap=true := by decide +kernel
theorem certified3536swap : Certified (graph core3536) (root 7) 6 0 :=
  of_native_maps core3536 DegreeTwoThreeSpectrum4174.graph DegreeTwoThreeSpectrum4176.graph
    sourceMap3536swap fusedMap3536swap sourceMap3536swap_checked fusedMap3536swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3536
#print axioms sourceMap3536swap_checked
#print axioms fusedMap3536swap_checked
#print axioms certified3536swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3719 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap3719 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3719 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3719_checked : acceptsGraphIso
    (source (graph core3719) (root 6) 0 8) DegreeTwoThreeSpectrum5507.graph sourceMap3719=true := by decide +kernel
theorem fusedMap3719_checked : acceptsGraphIso
    (fused (graph core3719) (root 6) 0 8) DegreeTwoThreeSpectrum5015.graph fusedMap3719=true := by decide +kernel
theorem certified3719 : Certified (graph core3719) (root 6) 0 8 :=
  of_native_maps core3719 DegreeTwoThreeSpectrum5507.graph DegreeTwoThreeSpectrum5015.graph
    sourceMap3719 fusedMap3719 sourceMap3719_checked fusedMap3719_checked
    DegreeTwoThreeFiniteComparisons.comparison3719
#print axioms sourceMap3719_checked
#print axioms fusedMap3719_checked
#print axioms certified3719
def sourceMap3719swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3719swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3719swap_checked : acceptsGraphIso
    (source (graph core3719) (root 6) 8 0) DegreeTwoThreeSpectrum5507.graph sourceMap3719swap=true := by decide +kernel
theorem fusedMap3719swap_checked : acceptsGraphIso
    (fused (graph core3719) (root 6) 8 0) DegreeTwoThreeSpectrum5015.graph fusedMap3719swap=true := by decide +kernel
theorem certified3719swap : Certified (graph core3719) (root 6) 8 0 :=
  of_native_maps core3719 DegreeTwoThreeSpectrum5507.graph DegreeTwoThreeSpectrum5015.graph
    sourceMap3719swap fusedMap3719swap sourceMap3719swap_checked fusedMap3719swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3719
#print axioms sourceMap3719swap_checked
#print axioms fusedMap3719swap_checked
#print axioms certified3719swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

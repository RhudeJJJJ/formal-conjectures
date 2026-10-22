/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2719 : Family 10 := level10.get ⟨871,by decide⟩
def sourceMap2719 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2719 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2719_checked : acceptsGraphIso
    (source (graph core2719) (root 10) 0 4) DegreeTwoThreeSpectrum6929.graph sourceMap2719=true := by decide +kernel
theorem fusedMap2719_checked : acceptsGraphIso
    (fused (graph core2719) (root 10) 0 4) DegreeTwoThreeSpectrum5715.graph fusedMap2719=true := by decide +kernel
theorem certified2719 : Certified (graph core2719) (root 10) 0 4 :=
  of_native_maps core2719 DegreeTwoThreeSpectrum6929.graph DegreeTwoThreeSpectrum5715.graph
    sourceMap2719 fusedMap2719 sourceMap2719_checked fusedMap2719_checked
    DegreeTwoThreeFiniteComparisons.comparison2719
#print axioms sourceMap2719_checked
#print axioms fusedMap2719_checked
#print axioms certified2719
def sourceMap2719swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2719swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2719swap_checked : acceptsGraphIso
    (source (graph core2719) (root 10) 4 0) DegreeTwoThreeSpectrum6929.graph sourceMap2719swap=true := by decide +kernel
theorem fusedMap2719swap_checked : acceptsGraphIso
    (fused (graph core2719) (root 10) 4 0) DegreeTwoThreeSpectrum5715.graph fusedMap2719swap=true := by decide +kernel
theorem certified2719swap : Certified (graph core2719) (root 10) 4 0 :=
  of_native_maps core2719 DegreeTwoThreeSpectrum6929.graph DegreeTwoThreeSpectrum5715.graph
    sourceMap2719swap fusedMap2719swap sourceMap2719swap_checked fusedMap2719swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2719
#print axioms sourceMap2719swap_checked
#print axioms fusedMap2719swap_checked
#print axioms certified2719swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

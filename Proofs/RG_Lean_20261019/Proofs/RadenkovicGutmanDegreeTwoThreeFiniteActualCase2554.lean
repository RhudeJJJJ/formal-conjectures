/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2554 : Family 10 := level10.get ⟨397,by decide⟩
def sourceMap2554 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2554 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2554_checked : acceptsGraphIso
    (source (graph core2554) (root 10) 0 4) DegreeTwoThreeSpectrum5747.graph sourceMap2554=true := by decide +kernel
theorem fusedMap2554_checked : acceptsGraphIso
    (fused (graph core2554) (root 10) 0 4) DegreeTwoThreeSpectrum5748.graph fusedMap2554=true := by decide +kernel
theorem certified2554 : Certified (graph core2554) (root 10) 0 4 :=
  of_native_maps core2554 DegreeTwoThreeSpectrum5747.graph DegreeTwoThreeSpectrum5748.graph
    sourceMap2554 fusedMap2554 sourceMap2554_checked fusedMap2554_checked
    DegreeTwoThreeFiniteComparisons.comparison2554
#print axioms sourceMap2554_checked
#print axioms fusedMap2554_checked
#print axioms certified2554
def sourceMap2554swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2554swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2554swap_checked : acceptsGraphIso
    (source (graph core2554) (root 10) 4 0) DegreeTwoThreeSpectrum5747.graph sourceMap2554swap=true := by decide +kernel
theorem fusedMap2554swap_checked : acceptsGraphIso
    (fused (graph core2554) (root 10) 4 0) DegreeTwoThreeSpectrum5748.graph fusedMap2554swap=true := by decide +kernel
theorem certified2554swap : Certified (graph core2554) (root 10) 4 0 :=
  of_native_maps core2554 DegreeTwoThreeSpectrum5747.graph DegreeTwoThreeSpectrum5748.graph
    sourceMap2554swap fusedMap2554swap sourceMap2554swap_checked fusedMap2554swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2554
#print axioms sourceMap2554swap_checked
#print axioms fusedMap2554swap_checked
#print axioms certified2554swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

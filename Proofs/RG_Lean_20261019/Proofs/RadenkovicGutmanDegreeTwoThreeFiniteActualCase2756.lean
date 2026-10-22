/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2756 : Family 10 := level10.get ⟨962,by decide⟩
def sourceMap2756 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2756 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2756_checked : acceptsGraphIso
    (source (graph core2756) (root 10) 0 4) DegreeTwoThreeSpectrum7034.graph sourceMap2756=true := by decide +kernel
theorem fusedMap2756_checked : acceptsGraphIso
    (fused (graph core2756) (root 10) 0 4) DegreeTwoThreeSpectrum5874.graph fusedMap2756=true := by decide +kernel
theorem certified2756 : Certified (graph core2756) (root 10) 0 4 :=
  of_native_maps core2756 DegreeTwoThreeSpectrum7034.graph DegreeTwoThreeSpectrum5874.graph
    sourceMap2756 fusedMap2756 sourceMap2756_checked fusedMap2756_checked
    DegreeTwoThreeFiniteComparisons.comparison2756
#print axioms sourceMap2756_checked
#print axioms fusedMap2756_checked
#print axioms certified2756
def sourceMap2756swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2756swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2756swap_checked : acceptsGraphIso
    (source (graph core2756) (root 10) 4 0) DegreeTwoThreeSpectrum7034.graph sourceMap2756swap=true := by decide +kernel
theorem fusedMap2756swap_checked : acceptsGraphIso
    (fused (graph core2756) (root 10) 4 0) DegreeTwoThreeSpectrum5874.graph fusedMap2756swap=true := by decide +kernel
theorem certified2756swap : Certified (graph core2756) (root 10) 4 0 :=
  of_native_maps core2756 DegreeTwoThreeSpectrum7034.graph DegreeTwoThreeSpectrum5874.graph
    sourceMap2756swap fusedMap2756swap sourceMap2756swap_checked fusedMap2756swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2756
#print axioms sourceMap2756swap_checked
#print axioms fusedMap2756swap_checked
#print axioms certified2756swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

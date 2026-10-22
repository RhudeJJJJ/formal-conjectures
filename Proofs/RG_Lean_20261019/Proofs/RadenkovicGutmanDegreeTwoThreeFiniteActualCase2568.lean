/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2568 : Family 10 := level10.get ⟨441,by decide⟩
def sourceMap2568 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2568 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2568_checked : acceptsGraphIso
    (source (graph core2568) (root 10) 0 4) DegreeTwoThreeSpectrum5855.graph sourceMap2568=true := by decide +kernel
theorem fusedMap2568_checked : acceptsGraphIso
    (fused (graph core2568) (root 10) 0 4) DegreeTwoThreeSpectrum5856.graph fusedMap2568=true := by decide +kernel
theorem certified2568 : Certified (graph core2568) (root 10) 0 4 :=
  of_native_maps core2568 DegreeTwoThreeSpectrum5855.graph DegreeTwoThreeSpectrum5856.graph
    sourceMap2568 fusedMap2568 sourceMap2568_checked fusedMap2568_checked
    DegreeTwoThreeFiniteComparisons.comparison2568
#print axioms sourceMap2568_checked
#print axioms fusedMap2568_checked
#print axioms certified2568
def sourceMap2568swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2568swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2568swap_checked : acceptsGraphIso
    (source (graph core2568) (root 10) 4 0) DegreeTwoThreeSpectrum5855.graph sourceMap2568swap=true := by decide +kernel
theorem fusedMap2568swap_checked : acceptsGraphIso
    (fused (graph core2568) (root 10) 4 0) DegreeTwoThreeSpectrum5856.graph fusedMap2568swap=true := by decide +kernel
theorem certified2568swap : Certified (graph core2568) (root 10) 4 0 :=
  of_native_maps core2568 DegreeTwoThreeSpectrum5855.graph DegreeTwoThreeSpectrum5856.graph
    sourceMap2568swap fusedMap2568swap sourceMap2568swap_checked fusedMap2568swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2568
#print axioms sourceMap2568swap_checked
#print axioms fusedMap2568swap_checked
#print axioms certified2568swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

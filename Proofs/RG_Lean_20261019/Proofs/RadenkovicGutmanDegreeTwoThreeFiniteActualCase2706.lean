/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2706 : Family 10 := level10.get ⟨836,by decide⟩
def sourceMap2706 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2706 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2706_checked : acceptsGraphIso
    (source (graph core2706) (root 10) 0 4) DegreeTwoThreeSpectrum6863.graph sourceMap2706=true := by decide +kernel
theorem fusedMap2706_checked : acceptsGraphIso
    (fused (graph core2706) (root 10) 0 4) DegreeTwoThreeSpectrum5664.graph fusedMap2706=true := by decide +kernel
theorem certified2706 : Certified (graph core2706) (root 10) 0 4 :=
  of_native_maps core2706 DegreeTwoThreeSpectrum6863.graph DegreeTwoThreeSpectrum5664.graph
    sourceMap2706 fusedMap2706 sourceMap2706_checked fusedMap2706_checked
    DegreeTwoThreeFiniteComparisons.comparison2706
#print axioms sourceMap2706_checked
#print axioms fusedMap2706_checked
#print axioms certified2706
def sourceMap2706swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2706swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2706swap_checked : acceptsGraphIso
    (source (graph core2706) (root 10) 4 0) DegreeTwoThreeSpectrum6863.graph sourceMap2706swap=true := by decide +kernel
theorem fusedMap2706swap_checked : acceptsGraphIso
    (fused (graph core2706) (root 10) 4 0) DegreeTwoThreeSpectrum5664.graph fusedMap2706swap=true := by decide +kernel
theorem certified2706swap : Certified (graph core2706) (root 10) 4 0 :=
  of_native_maps core2706 DegreeTwoThreeSpectrum6863.graph DegreeTwoThreeSpectrum5664.graph
    sourceMap2706swap fusedMap2706swap sourceMap2706swap_checked fusedMap2706swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2706
#print axioms sourceMap2706swap_checked
#print axioms fusedMap2706swap_checked
#print axioms certified2706swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

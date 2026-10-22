/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2597 : Family 10 := level10.get ⟨524,by decide⟩
def sourceMap2597 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2597 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2597_checked : acceptsGraphIso
    (source (graph core2597) (root 10) 0 4) DegreeTwoThreeSpectrum6089.graph sourceMap2597=true := by decide +kernel
theorem fusedMap2597_checked : acceptsGraphIso
    (fused (graph core2597) (root 10) 0 4) DegreeTwoThreeSpectrum5167.graph fusedMap2597=true := by decide +kernel
theorem certified2597 : Certified (graph core2597) (root 10) 0 4 :=
  of_native_maps core2597 DegreeTwoThreeSpectrum6089.graph DegreeTwoThreeSpectrum5167.graph
    sourceMap2597 fusedMap2597 sourceMap2597_checked fusedMap2597_checked
    DegreeTwoThreeFiniteComparisons.comparison2597
#print axioms sourceMap2597_checked
#print axioms fusedMap2597_checked
#print axioms certified2597
def sourceMap2597swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2597swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2597swap_checked : acceptsGraphIso
    (source (graph core2597) (root 10) 4 0) DegreeTwoThreeSpectrum6089.graph sourceMap2597swap=true := by decide +kernel
theorem fusedMap2597swap_checked : acceptsGraphIso
    (fused (graph core2597) (root 10) 4 0) DegreeTwoThreeSpectrum5167.graph fusedMap2597swap=true := by decide +kernel
theorem certified2597swap : Certified (graph core2597) (root 10) 4 0 :=
  of_native_maps core2597 DegreeTwoThreeSpectrum6089.graph DegreeTwoThreeSpectrum5167.graph
    sourceMap2597swap fusedMap2597swap sourceMap2597swap_checked fusedMap2597swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2597
#print axioms sourceMap2597swap_checked
#print axioms fusedMap2597swap_checked
#print axioms certified2597swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

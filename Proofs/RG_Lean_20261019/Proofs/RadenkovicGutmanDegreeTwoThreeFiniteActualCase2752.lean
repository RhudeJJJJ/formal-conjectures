/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2752 : Family 10 := level10.get ⟨954,by decide⟩
def sourceMap2752 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2752 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2752_checked : acceptsGraphIso
    (source (graph core2752) (root 10) 0 4) DegreeTwoThreeSpectrum7030.graph sourceMap2752=true := by decide +kernel
theorem fusedMap2752_checked : acceptsGraphIso
    (fused (graph core2752) (root 10) 0 4) DegreeTwoThreeSpectrum5857.graph fusedMap2752=true := by decide +kernel
theorem certified2752 : Certified (graph core2752) (root 10) 0 4 :=
  of_native_maps core2752 DegreeTwoThreeSpectrum7030.graph DegreeTwoThreeSpectrum5857.graph
    sourceMap2752 fusedMap2752 sourceMap2752_checked fusedMap2752_checked
    DegreeTwoThreeFiniteComparisons.comparison2752
#print axioms sourceMap2752_checked
#print axioms fusedMap2752_checked
#print axioms certified2752
def sourceMap2752swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2752swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2752swap_checked : acceptsGraphIso
    (source (graph core2752) (root 10) 4 0) DegreeTwoThreeSpectrum7030.graph sourceMap2752swap=true := by decide +kernel
theorem fusedMap2752swap_checked : acceptsGraphIso
    (fused (graph core2752) (root 10) 4 0) DegreeTwoThreeSpectrum5857.graph fusedMap2752swap=true := by decide +kernel
theorem certified2752swap : Certified (graph core2752) (root 10) 4 0 :=
  of_native_maps core2752 DegreeTwoThreeSpectrum7030.graph DegreeTwoThreeSpectrum5857.graph
    sourceMap2752swap fusedMap2752swap sourceMap2752swap_checked fusedMap2752swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2752
#print axioms sourceMap2752swap_checked
#print axioms fusedMap2752swap_checked
#print axioms certified2752swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

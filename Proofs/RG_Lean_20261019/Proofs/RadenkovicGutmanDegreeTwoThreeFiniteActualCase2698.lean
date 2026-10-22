/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2698 : Family 10 := level10.get ⟨815,by decide⟩
def sourceMap2698 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2698 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2698_checked : acceptsGraphIso
    (source (graph core2698) (root 10) 0 4) DegreeTwoThreeSpectrum6775.graph sourceMap2698=true := by decide +kernel
theorem fusedMap2698_checked : acceptsGraphIso
    (fused (graph core2698) (root 10) 0 4) DegreeTwoThreeSpectrum5614.graph fusedMap2698=true := by decide +kernel
theorem certified2698 : Certified (graph core2698) (root 10) 0 4 :=
  of_native_maps core2698 DegreeTwoThreeSpectrum6775.graph DegreeTwoThreeSpectrum5614.graph
    sourceMap2698 fusedMap2698 sourceMap2698_checked fusedMap2698_checked
    DegreeTwoThreeFiniteComparisons.comparison2698
#print axioms sourceMap2698_checked
#print axioms fusedMap2698_checked
#print axioms certified2698
def sourceMap2698swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2698swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2698swap_checked : acceptsGraphIso
    (source (graph core2698) (root 10) 4 0) DegreeTwoThreeSpectrum6775.graph sourceMap2698swap=true := by decide +kernel
theorem fusedMap2698swap_checked : acceptsGraphIso
    (fused (graph core2698) (root 10) 4 0) DegreeTwoThreeSpectrum5614.graph fusedMap2698swap=true := by decide +kernel
theorem certified2698swap : Certified (graph core2698) (root 10) 4 0 :=
  of_native_maps core2698 DegreeTwoThreeSpectrum6775.graph DegreeTwoThreeSpectrum5614.graph
    sourceMap2698swap fusedMap2698swap sourceMap2698swap_checked fusedMap2698swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2698
#print axioms sourceMap2698swap_checked
#print axioms fusedMap2698swap_checked
#print axioms certified2698swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

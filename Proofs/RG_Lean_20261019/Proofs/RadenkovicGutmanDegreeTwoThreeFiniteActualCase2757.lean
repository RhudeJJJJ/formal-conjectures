/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2757 : Family 10 := level10.get ⟨963,by decide⟩
def sourceMap2757 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2757 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2757_checked : acceptsGraphIso
    (source (graph core2757) (root 10) 0 4) DegreeTwoThreeSpectrum7035.graph sourceMap2757=true := by decide +kernel
theorem fusedMap2757_checked : acceptsGraphIso
    (fused (graph core2757) (root 10) 0 4) DegreeTwoThreeSpectrum5875.graph fusedMap2757=true := by decide +kernel
theorem certified2757 : Certified (graph core2757) (root 10) 0 4 :=
  of_native_maps core2757 DegreeTwoThreeSpectrum7035.graph DegreeTwoThreeSpectrum5875.graph
    sourceMap2757 fusedMap2757 sourceMap2757_checked fusedMap2757_checked
    DegreeTwoThreeFiniteComparisons.comparison2757
#print axioms sourceMap2757_checked
#print axioms fusedMap2757_checked
#print axioms certified2757
def sourceMap2757swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2757swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2757swap_checked : acceptsGraphIso
    (source (graph core2757) (root 10) 4 0) DegreeTwoThreeSpectrum7035.graph sourceMap2757swap=true := by decide +kernel
theorem fusedMap2757swap_checked : acceptsGraphIso
    (fused (graph core2757) (root 10) 4 0) DegreeTwoThreeSpectrum5875.graph fusedMap2757swap=true := by decide +kernel
theorem certified2757swap : Certified (graph core2757) (root 10) 4 0 :=
  of_native_maps core2757 DegreeTwoThreeSpectrum7035.graph DegreeTwoThreeSpectrum5875.graph
    sourceMap2757swap fusedMap2757swap sourceMap2757swap_checked fusedMap2757swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2757
#print axioms sourceMap2757swap_checked
#print axioms fusedMap2757swap_checked
#print axioms certified2757swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

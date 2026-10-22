/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2624 : Family 10 := level10.get ⟨608,by decide⟩
def sourceMap2624 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2624 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2624_checked : acceptsGraphIso
    (source (graph core2624) (root 10) 0 4) DegreeTwoThreeSpectrum6327.graph sourceMap2624=true := by decide +kernel
theorem fusedMap2624_checked : acceptsGraphIso
    (fused (graph core2624) (root 10) 0 4) DegreeTwoThreeSpectrum5287.graph fusedMap2624=true := by decide +kernel
theorem certified2624 : Certified (graph core2624) (root 10) 0 4 :=
  of_native_maps core2624 DegreeTwoThreeSpectrum6327.graph DegreeTwoThreeSpectrum5287.graph
    sourceMap2624 fusedMap2624 sourceMap2624_checked fusedMap2624_checked
    DegreeTwoThreeFiniteComparisons.comparison2624
#print axioms sourceMap2624_checked
#print axioms fusedMap2624_checked
#print axioms certified2624
def sourceMap2624swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2624swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2624swap_checked : acceptsGraphIso
    (source (graph core2624) (root 10) 4 0) DegreeTwoThreeSpectrum6327.graph sourceMap2624swap=true := by decide +kernel
theorem fusedMap2624swap_checked : acceptsGraphIso
    (fused (graph core2624) (root 10) 4 0) DegreeTwoThreeSpectrum5287.graph fusedMap2624swap=true := by decide +kernel
theorem certified2624swap : Certified (graph core2624) (root 10) 4 0 :=
  of_native_maps core2624 DegreeTwoThreeSpectrum6327.graph DegreeTwoThreeSpectrum5287.graph
    sourceMap2624swap fusedMap2624swap sourceMap2624swap_checked fusedMap2624swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2624
#print axioms sourceMap2624swap_checked
#print axioms fusedMap2624swap_checked
#print axioms certified2624swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

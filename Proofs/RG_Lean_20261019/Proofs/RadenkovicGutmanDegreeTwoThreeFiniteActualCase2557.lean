/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2557 : Family 10 := level10.get ⟨407,by decide⟩
def sourceMap2557 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2557 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2557_checked : acceptsGraphIso
    (source (graph core2557) (root 10) 0 4) DegreeTwoThreeSpectrum5775.graph sourceMap2557=true := by decide +kernel
theorem fusedMap2557_checked : acceptsGraphIso
    (fused (graph core2557) (root 10) 0 4) DegreeTwoThreeSpectrum5776.graph fusedMap2557=true := by decide +kernel
theorem certified2557 : Certified (graph core2557) (root 10) 0 4 :=
  of_native_maps core2557 DegreeTwoThreeSpectrum5775.graph DegreeTwoThreeSpectrum5776.graph
    sourceMap2557 fusedMap2557 sourceMap2557_checked fusedMap2557_checked
    DegreeTwoThreeFiniteComparisons.comparison2557
#print axioms sourceMap2557_checked
#print axioms fusedMap2557_checked
#print axioms certified2557
def sourceMap2557swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2557swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2557swap_checked : acceptsGraphIso
    (source (graph core2557) (root 10) 4 0) DegreeTwoThreeSpectrum5775.graph sourceMap2557swap=true := by decide +kernel
theorem fusedMap2557swap_checked : acceptsGraphIso
    (fused (graph core2557) (root 10) 4 0) DegreeTwoThreeSpectrum5776.graph fusedMap2557swap=true := by decide +kernel
theorem certified2557swap : Certified (graph core2557) (root 10) 4 0 :=
  of_native_maps core2557 DegreeTwoThreeSpectrum5775.graph DegreeTwoThreeSpectrum5776.graph
    sourceMap2557swap fusedMap2557swap sourceMap2557swap_checked fusedMap2557swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2557
#print axioms sourceMap2557swap_checked
#print axioms fusedMap2557swap_checked
#print axioms certified2557swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

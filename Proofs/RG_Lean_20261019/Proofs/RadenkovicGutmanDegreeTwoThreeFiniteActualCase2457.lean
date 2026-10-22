/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2457 : Family 10 := level10.get ⟨32,by decide⟩
def sourceMap2457 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2457 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2457_checked : acceptsGraphIso
    (source (graph core2457) (root 10) 0 4) DegreeTwoThreeSpectrum5076.graph sourceMap2457=true := by decide +kernel
theorem fusedMap2457_checked : acceptsGraphIso
    (fused (graph core2457) (root 10) 0 4) DegreeTwoThreeSpectrum5079.graph fusedMap2457=true := by decide +kernel
theorem certified2457 : Certified (graph core2457) (root 10) 0 4 :=
  of_native_maps core2457 DegreeTwoThreeSpectrum5076.graph DegreeTwoThreeSpectrum5079.graph
    sourceMap2457 fusedMap2457 sourceMap2457_checked fusedMap2457_checked
    DegreeTwoThreeFiniteComparisons.comparison2457
#print axioms sourceMap2457_checked
#print axioms fusedMap2457_checked
#print axioms certified2457
def sourceMap2457swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2457swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2457swap_checked : acceptsGraphIso
    (source (graph core2457) (root 10) 4 0) DegreeTwoThreeSpectrum5076.graph sourceMap2457swap=true := by decide +kernel
theorem fusedMap2457swap_checked : acceptsGraphIso
    (fused (graph core2457) (root 10) 4 0) DegreeTwoThreeSpectrum5079.graph fusedMap2457swap=true := by decide +kernel
theorem certified2457swap : Certified (graph core2457) (root 10) 4 0 :=
  of_native_maps core2457 DegreeTwoThreeSpectrum5076.graph DegreeTwoThreeSpectrum5079.graph
    sourceMap2457swap fusedMap2457swap sourceMap2457swap_checked fusedMap2457swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2457
#print axioms sourceMap2457swap_checked
#print axioms fusedMap2457swap_checked
#print axioms certified2457swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

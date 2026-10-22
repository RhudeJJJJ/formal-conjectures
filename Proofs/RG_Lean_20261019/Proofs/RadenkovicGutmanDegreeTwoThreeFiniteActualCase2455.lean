/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2455 : Family 10 := level10.get ⟨17,by decide⟩
def sourceMap2455 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2455 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2455_checked : acceptsGraphIso
    (source (graph core2455) (root 10) 0 4) DegreeTwoThreeSpectrum5003.graph sourceMap2455=true := by decide +kernel
theorem fusedMap2455_checked : acceptsGraphIso
    (fused (graph core2455) (root 10) 0 4) DegreeTwoThreeSpectrum5006.graph fusedMap2455=true := by decide +kernel
theorem certified2455 : Certified (graph core2455) (root 10) 0 4 :=
  of_native_maps core2455 DegreeTwoThreeSpectrum5003.graph DegreeTwoThreeSpectrum5006.graph
    sourceMap2455 fusedMap2455 sourceMap2455_checked fusedMap2455_checked
    DegreeTwoThreeFiniteComparisons.comparison2455
#print axioms sourceMap2455_checked
#print axioms fusedMap2455_checked
#print axioms certified2455
def sourceMap2455swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2455swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2455swap_checked : acceptsGraphIso
    (source (graph core2455) (root 10) 4 0) DegreeTwoThreeSpectrum5003.graph sourceMap2455swap=true := by decide +kernel
theorem fusedMap2455swap_checked : acceptsGraphIso
    (fused (graph core2455) (root 10) 4 0) DegreeTwoThreeSpectrum5006.graph fusedMap2455swap=true := by decide +kernel
theorem certified2455swap : Certified (graph core2455) (root 10) 4 0 :=
  of_native_maps core2455 DegreeTwoThreeSpectrum5003.graph DegreeTwoThreeSpectrum5006.graph
    sourceMap2455swap fusedMap2455swap sourceMap2455swap_checked fusedMap2455swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2455
#print axioms sourceMap2455swap_checked
#print axioms fusedMap2455swap_checked
#print axioms certified2455swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

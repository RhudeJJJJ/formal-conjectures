/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2456 : Family 10 := level10.get ⟨25,by decide⟩
def sourceMap2456 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2456 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2456_checked : acceptsGraphIso
    (source (graph core2456) (root 10) 0 4) DegreeTwoThreeSpectrum5043.graph sourceMap2456=true := by decide +kernel
theorem fusedMap2456_checked : acceptsGraphIso
    (fused (graph core2456) (root 10) 0 4) DegreeTwoThreeSpectrum5046.graph fusedMap2456=true := by decide +kernel
theorem certified2456 : Certified (graph core2456) (root 10) 0 4 :=
  of_native_maps core2456 DegreeTwoThreeSpectrum5043.graph DegreeTwoThreeSpectrum5046.graph
    sourceMap2456 fusedMap2456 sourceMap2456_checked fusedMap2456_checked
    DegreeTwoThreeFiniteComparisons.comparison2456
#print axioms sourceMap2456_checked
#print axioms fusedMap2456_checked
#print axioms certified2456
def sourceMap2456swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2456swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2456swap_checked : acceptsGraphIso
    (source (graph core2456) (root 10) 4 0) DegreeTwoThreeSpectrum5043.graph sourceMap2456swap=true := by decide +kernel
theorem fusedMap2456swap_checked : acceptsGraphIso
    (fused (graph core2456) (root 10) 4 0) DegreeTwoThreeSpectrum5046.graph fusedMap2456swap=true := by decide +kernel
theorem certified2456swap : Certified (graph core2456) (root 10) 4 0 :=
  of_native_maps core2456 DegreeTwoThreeSpectrum5043.graph DegreeTwoThreeSpectrum5046.graph
    sourceMap2456swap fusedMap2456swap sourceMap2456swap_checked fusedMap2456swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2456
#print axioms sourceMap2456swap_checked
#print axioms fusedMap2456swap_checked
#print axioms certified2456swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

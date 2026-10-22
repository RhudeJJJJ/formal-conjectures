/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2490 : Family 10 := level10.get ⟨174,by decide⟩
def sourceMap2490 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,8,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2490 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2490_checked : acceptsGraphIso
    (source (graph core2490) (root 10) 0 4) DegreeTwoThreeSpectrum5947.graph sourceMap2490=true := by decide +kernel
theorem fusedMap2490_checked : acceptsGraphIso
    (fused (graph core2490) (root 10) 0 4) DegreeTwoThreeSpectrum5118.graph fusedMap2490=true := by decide +kernel
theorem certified2490 : Certified (graph core2490) (root 10) 0 4 :=
  of_native_maps core2490 DegreeTwoThreeSpectrum5947.graph DegreeTwoThreeSpectrum5118.graph
    sourceMap2490 fusedMap2490 sourceMap2490_checked fusedMap2490_checked
    DegreeTwoThreeFiniteComparisons.comparison2490
#print axioms sourceMap2490_checked
#print axioms fusedMap2490_checked
#print axioms certified2490
def sourceMap2490swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,2,3,4,5,6,8] (sourceLabel 10 4 0 v)
def fusedMap2490swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2490swap_checked : acceptsGraphIso
    (source (graph core2490) (root 10) 4 0) DegreeTwoThreeSpectrum5947.graph sourceMap2490swap=true := by decide +kernel
theorem fusedMap2490swap_checked : acceptsGraphIso
    (fused (graph core2490) (root 10) 4 0) DegreeTwoThreeSpectrum5118.graph fusedMap2490swap=true := by decide +kernel
theorem certified2490swap : Certified (graph core2490) (root 10) 4 0 :=
  of_native_maps core2490 DegreeTwoThreeSpectrum5947.graph DegreeTwoThreeSpectrum5118.graph
    sourceMap2490swap fusedMap2490swap sourceMap2490swap_checked fusedMap2490swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2490
#print axioms sourceMap2490swap_checked
#print axioms fusedMap2490swap_checked
#print axioms certified2490swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

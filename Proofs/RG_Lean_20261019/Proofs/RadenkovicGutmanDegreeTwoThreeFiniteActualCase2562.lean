/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2562 : Family 10 := level10.get ⟨421,by decide⟩
def sourceMap2562 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2562 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2562_checked : acceptsGraphIso
    (source (graph core2562) (root 10) 0 4) DegreeTwoThreeSpectrum5805.graph sourceMap2562=true := by decide +kernel
theorem fusedMap2562_checked : acceptsGraphIso
    (fused (graph core2562) (root 10) 0 4) DegreeTwoThreeSpectrum5806.graph fusedMap2562=true := by decide +kernel
theorem certified2562 : Certified (graph core2562) (root 10) 0 4 :=
  of_native_maps core2562 DegreeTwoThreeSpectrum5805.graph DegreeTwoThreeSpectrum5806.graph
    sourceMap2562 fusedMap2562 sourceMap2562_checked fusedMap2562_checked
    DegreeTwoThreeFiniteComparisons.comparison2562
#print axioms sourceMap2562_checked
#print axioms fusedMap2562_checked
#print axioms certified2562
def sourceMap2562swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2562swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2562swap_checked : acceptsGraphIso
    (source (graph core2562) (root 10) 4 0) DegreeTwoThreeSpectrum5805.graph sourceMap2562swap=true := by decide +kernel
theorem fusedMap2562swap_checked : acceptsGraphIso
    (fused (graph core2562) (root 10) 4 0) DegreeTwoThreeSpectrum5806.graph fusedMap2562swap=true := by decide +kernel
theorem certified2562swap : Certified (graph core2562) (root 10) 4 0 :=
  of_native_maps core2562 DegreeTwoThreeSpectrum5805.graph DegreeTwoThreeSpectrum5806.graph
    sourceMap2562swap fusedMap2562swap sourceMap2562swap_checked fusedMap2562swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2562
#print axioms sourceMap2562swap_checked
#print axioms fusedMap2562swap_checked
#print axioms certified2562swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

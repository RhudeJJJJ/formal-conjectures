/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2533 : Family 10 := level10.get ⟨328,by decide⟩
def sourceMap2533 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2533 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2533_checked : acceptsGraphIso
    (source (graph core2533) (root 10) 0 4) DegreeTwoThreeSpectrum5560.graph sourceMap2533=true := by decide +kernel
theorem fusedMap2533_checked : acceptsGraphIso
    (fused (graph core2533) (root 10) 0 4) DegreeTwoThreeSpectrum5561.graph fusedMap2533=true := by decide +kernel
theorem certified2533 : Certified (graph core2533) (root 10) 0 4 :=
  of_native_maps core2533 DegreeTwoThreeSpectrum5560.graph DegreeTwoThreeSpectrum5561.graph
    sourceMap2533 fusedMap2533 sourceMap2533_checked fusedMap2533_checked
    DegreeTwoThreeFiniteComparisons.comparison2533
#print axioms sourceMap2533_checked
#print axioms fusedMap2533_checked
#print axioms certified2533
def sourceMap2533swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2533swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2533swap_checked : acceptsGraphIso
    (source (graph core2533) (root 10) 4 0) DegreeTwoThreeSpectrum5560.graph sourceMap2533swap=true := by decide +kernel
theorem fusedMap2533swap_checked : acceptsGraphIso
    (fused (graph core2533) (root 10) 4 0) DegreeTwoThreeSpectrum5561.graph fusedMap2533swap=true := by decide +kernel
theorem certified2533swap : Certified (graph core2533) (root 10) 4 0 :=
  of_native_maps core2533 DegreeTwoThreeSpectrum5560.graph DegreeTwoThreeSpectrum5561.graph
    sourceMap2533swap fusedMap2533swap sourceMap2533swap_checked fusedMap2533swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2533
#print axioms sourceMap2533swap_checked
#print axioms fusedMap2533swap_checked
#print axioms certified2533swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

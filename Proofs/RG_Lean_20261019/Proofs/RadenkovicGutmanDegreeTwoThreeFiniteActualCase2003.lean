/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2003 : Family 10 := level10.get ⟨1631,by decide⟩
def sourceMap2003 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap2003 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2003_checked : acceptsGraphIso
    (source (graph core2003) (root 10) 0 2) DegreeTwoThreeSpectrum3790.graph sourceMap2003=true := by decide +kernel
theorem fusedMap2003_checked : acceptsGraphIso
    (fused (graph core2003) (root 10) 0 2) DegreeTwoThreeSpectrum3175.graph fusedMap2003=true := by decide +kernel
theorem certified2003 : Certified (graph core2003) (root 10) 0 2 :=
  of_native_maps core2003 DegreeTwoThreeSpectrum3790.graph DegreeTwoThreeSpectrum3175.graph
    sourceMap2003 fusedMap2003 sourceMap2003_checked fusedMap2003_checked
    DegreeTwoThreeFiniteComparisons.comparison2003
#print axioms sourceMap2003_checked
#print axioms fusedMap2003_checked
#print axioms certified2003
def sourceMap2003swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap2003swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2003swap_checked : acceptsGraphIso
    (source (graph core2003) (root 10) 2 0) DegreeTwoThreeSpectrum3790.graph sourceMap2003swap=true := by decide +kernel
theorem fusedMap2003swap_checked : acceptsGraphIso
    (fused (graph core2003) (root 10) 2 0) DegreeTwoThreeSpectrum3175.graph fusedMap2003swap=true := by decide +kernel
theorem certified2003swap : Certified (graph core2003) (root 10) 2 0 :=
  of_native_maps core2003 DegreeTwoThreeSpectrum3790.graph DegreeTwoThreeSpectrum3175.graph
    sourceMap2003swap fusedMap2003swap sourceMap2003swap_checked fusedMap2003swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2003
#print axioms sourceMap2003swap_checked
#print axioms fusedMap2003swap_checked
#print axioms certified2003swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

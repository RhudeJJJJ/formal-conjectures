/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2589 : Family 10 := level10.get ⟨490,by decide⟩
def sourceMap2589 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,10,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2589 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 0 4 v)
theorem sourceMap2589_checked : acceptsGraphIso
    (source (graph core2589) (root 10) 0 4) DegreeTwoThreeSpectrum5921.graph sourceMap2589=true := by decide +kernel
theorem fusedMap2589_checked : acceptsGraphIso
    (fused (graph core2589) (root 10) 0 4) DegreeTwoThreeSpectrum5955.graph fusedMap2589=true := by decide +kernel
theorem certified2589 : Certified (graph core2589) (root 10) 0 4 :=
  of_native_maps core2589 DegreeTwoThreeSpectrum5921.graph DegreeTwoThreeSpectrum5955.graph
    sourceMap2589 fusedMap2589 sourceMap2589_checked fusedMap2589_checked
    DegreeTwoThreeFiniteComparisons.comparison2589
#print axioms sourceMap2589_checked
#print axioms fusedMap2589_checked
#print axioms certified2589
def sourceMap2589swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,1,2,3,4,5,10] (sourceLabel 10 4 0 v)
def fusedMap2589swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 4 0 v)
theorem sourceMap2589swap_checked : acceptsGraphIso
    (source (graph core2589) (root 10) 4 0) DegreeTwoThreeSpectrum5921.graph sourceMap2589swap=true := by decide +kernel
theorem fusedMap2589swap_checked : acceptsGraphIso
    (fused (graph core2589) (root 10) 4 0) DegreeTwoThreeSpectrum5955.graph fusedMap2589swap=true := by decide +kernel
theorem certified2589swap : Certified (graph core2589) (root 10) 4 0 :=
  of_native_maps core2589 DegreeTwoThreeSpectrum5921.graph DegreeTwoThreeSpectrum5955.graph
    sourceMap2589swap fusedMap2589swap sourceMap2589swap_checked fusedMap2589swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2589
#print axioms sourceMap2589swap_checked
#print axioms fusedMap2589swap_checked
#print axioms certified2589swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

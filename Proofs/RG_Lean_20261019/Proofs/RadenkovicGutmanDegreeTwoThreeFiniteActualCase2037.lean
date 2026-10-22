/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2037 : Family 10 := level10.get ⟨1729,by decide⟩
def sourceMap2037 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap2037 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2037_checked : acceptsGraphIso
    (source (graph core2037) (root 10) 0 2) DegreeTwoThreeSpectrum3834.graph sourceMap2037=true := by decide +kernel
theorem fusedMap2037_checked : acceptsGraphIso
    (fused (graph core2037) (root 10) 0 2) DegreeTwoThreeSpectrum3425.graph fusedMap2037=true := by decide +kernel
theorem certified2037 : Certified (graph core2037) (root 10) 0 2 :=
  of_native_maps core2037 DegreeTwoThreeSpectrum3834.graph DegreeTwoThreeSpectrum3425.graph
    sourceMap2037 fusedMap2037 sourceMap2037_checked fusedMap2037_checked
    DegreeTwoThreeFiniteComparisons.comparison2037
#print axioms sourceMap2037_checked
#print axioms fusedMap2037_checked
#print axioms certified2037
def sourceMap2037swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8,14] (sourceLabel 10 2 0 v)
def fusedMap2037swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2037swap_checked : acceptsGraphIso
    (source (graph core2037) (root 10) 2 0) DegreeTwoThreeSpectrum3834.graph sourceMap2037swap=true := by decide +kernel
theorem fusedMap2037swap_checked : acceptsGraphIso
    (fused (graph core2037) (root 10) 2 0) DegreeTwoThreeSpectrum3425.graph fusedMap2037swap=true := by decide +kernel
theorem certified2037swap : Certified (graph core2037) (root 10) 2 0 :=
  of_native_maps core2037 DegreeTwoThreeSpectrum3834.graph DegreeTwoThreeSpectrum3425.graph
    sourceMap2037swap fusedMap2037swap sourceMap2037swap_checked fusedMap2037swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2037
#print axioms sourceMap2037swap_checked
#print axioms fusedMap2037swap_checked
#print axioms certified2037swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

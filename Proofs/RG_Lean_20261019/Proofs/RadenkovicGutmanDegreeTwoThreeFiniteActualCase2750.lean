/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2750 : Family 10 := level10.get ⟨951,by decide⟩
def sourceMap2750 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2750 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2750_checked : acceptsGraphIso
    (source (graph core2750) (root 10) 0 4) DegreeTwoThreeSpectrum7028.graph sourceMap2750=true := by decide +kernel
theorem fusedMap2750_checked : acceptsGraphIso
    (fused (graph core2750) (root 10) 0 4) DegreeTwoThreeSpectrum5851.graph fusedMap2750=true := by decide +kernel
theorem certified2750 : Certified (graph core2750) (root 10) 0 4 :=
  of_native_maps core2750 DegreeTwoThreeSpectrum7028.graph DegreeTwoThreeSpectrum5851.graph
    sourceMap2750 fusedMap2750 sourceMap2750_checked fusedMap2750_checked
    DegreeTwoThreeFiniteComparisons.comparison2750
#print axioms sourceMap2750_checked
#print axioms fusedMap2750_checked
#print axioms certified2750
def sourceMap2750swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2750swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2750swap_checked : acceptsGraphIso
    (source (graph core2750) (root 10) 4 0) DegreeTwoThreeSpectrum7028.graph sourceMap2750swap=true := by decide +kernel
theorem fusedMap2750swap_checked : acceptsGraphIso
    (fused (graph core2750) (root 10) 4 0) DegreeTwoThreeSpectrum5851.graph fusedMap2750swap=true := by decide +kernel
theorem certified2750swap : Certified (graph core2750) (root 10) 4 0 :=
  of_native_maps core2750 DegreeTwoThreeSpectrum7028.graph DegreeTwoThreeSpectrum5851.graph
    sourceMap2750swap fusedMap2750swap sourceMap2750swap_checked fusedMap2750swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2750
#print axioms sourceMap2750swap_checked
#print axioms fusedMap2750swap_checked
#print axioms certified2750swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

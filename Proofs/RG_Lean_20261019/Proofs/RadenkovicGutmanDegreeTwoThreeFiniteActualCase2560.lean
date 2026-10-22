/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2560 : Family 10 := level10.get ⟨414,by decide⟩
def sourceMap2560 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2560 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2560_checked : acceptsGraphIso
    (source (graph core2560) (root 10) 0 4) DegreeTwoThreeSpectrum5790.graph sourceMap2560=true := by decide +kernel
theorem fusedMap2560_checked : acceptsGraphIso
    (fused (graph core2560) (root 10) 0 4) DegreeTwoThreeSpectrum5792.graph fusedMap2560=true := by decide +kernel
theorem certified2560 : Certified (graph core2560) (root 10) 0 4 :=
  of_native_maps core2560 DegreeTwoThreeSpectrum5790.graph DegreeTwoThreeSpectrum5792.graph
    sourceMap2560 fusedMap2560 sourceMap2560_checked fusedMap2560_checked
    DegreeTwoThreeFiniteComparisons.comparison2560
#print axioms sourceMap2560_checked
#print axioms fusedMap2560_checked
#print axioms certified2560
def sourceMap2560swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2560swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2560swap_checked : acceptsGraphIso
    (source (graph core2560) (root 10) 4 0) DegreeTwoThreeSpectrum5790.graph sourceMap2560swap=true := by decide +kernel
theorem fusedMap2560swap_checked : acceptsGraphIso
    (fused (graph core2560) (root 10) 4 0) DegreeTwoThreeSpectrum5792.graph fusedMap2560swap=true := by decide +kernel
theorem certified2560swap : Certified (graph core2560) (root 10) 4 0 :=
  of_native_maps core2560 DegreeTwoThreeSpectrum5790.graph DegreeTwoThreeSpectrum5792.graph
    sourceMap2560swap fusedMap2560swap sourceMap2560swap_checked fusedMap2560swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2560
#print axioms sourceMap2560swap_checked
#print axioms fusedMap2560swap_checked
#print axioms certified2560swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

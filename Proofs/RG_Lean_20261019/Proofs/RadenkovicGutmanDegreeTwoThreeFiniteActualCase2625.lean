/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2625 : Family 10 := level10.get ⟨609,by decide⟩
def sourceMap2625 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2625 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2625_checked : acceptsGraphIso
    (source (graph core2625) (root 10) 0 4) DegreeTwoThreeSpectrum6329.graph sourceMap2625=true := by decide +kernel
theorem fusedMap2625_checked : acceptsGraphIso
    (fused (graph core2625) (root 10) 0 4) DegreeTwoThreeSpectrum5289.graph fusedMap2625=true := by decide +kernel
theorem certified2625 : Certified (graph core2625) (root 10) 0 4 :=
  of_native_maps core2625 DegreeTwoThreeSpectrum6329.graph DegreeTwoThreeSpectrum5289.graph
    sourceMap2625 fusedMap2625 sourceMap2625_checked fusedMap2625_checked
    DegreeTwoThreeFiniteComparisons.comparison2625
#print axioms sourceMap2625_checked
#print axioms fusedMap2625_checked
#print axioms certified2625
def sourceMap2625swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2625swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2625swap_checked : acceptsGraphIso
    (source (graph core2625) (root 10) 4 0) DegreeTwoThreeSpectrum6329.graph sourceMap2625swap=true := by decide +kernel
theorem fusedMap2625swap_checked : acceptsGraphIso
    (fused (graph core2625) (root 10) 4 0) DegreeTwoThreeSpectrum5289.graph fusedMap2625swap=true := by decide +kernel
theorem certified2625swap : Certified (graph core2625) (root 10) 4 0 :=
  of_native_maps core2625 DegreeTwoThreeSpectrum6329.graph DegreeTwoThreeSpectrum5289.graph
    sourceMap2625swap fusedMap2625swap sourceMap2625swap_checked fusedMap2625swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2625
#print axioms sourceMap2625swap_checked
#print axioms fusedMap2625swap_checked
#print axioms certified2625swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

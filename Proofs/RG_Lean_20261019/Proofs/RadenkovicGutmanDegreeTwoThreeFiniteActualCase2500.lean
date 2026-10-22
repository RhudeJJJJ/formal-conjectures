/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2500 : Family 10 := level10.get ⟨209,by decide⟩
def sourceMap2500 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2500 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2500_checked : acceptsGraphIso
    (source (graph core2500) (root 10) 0 4) DegreeTwoThreeSpectrum5211.graph sourceMap2500=true := by decide +kernel
theorem fusedMap2500_checked : acceptsGraphIso
    (fused (graph core2500) (root 10) 0 4) DegreeTwoThreeSpectrum5212.graph fusedMap2500=true := by decide +kernel
theorem certified2500 : Certified (graph core2500) (root 10) 0 4 :=
  of_native_maps core2500 DegreeTwoThreeSpectrum5211.graph DegreeTwoThreeSpectrum5212.graph
    sourceMap2500 fusedMap2500 sourceMap2500_checked fusedMap2500_checked
    DegreeTwoThreeFiniteComparisons.comparison2500
#print axioms sourceMap2500_checked
#print axioms fusedMap2500_checked
#print axioms certified2500
def sourceMap2500swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2500swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2500swap_checked : acceptsGraphIso
    (source (graph core2500) (root 10) 4 0) DegreeTwoThreeSpectrum5211.graph sourceMap2500swap=true := by decide +kernel
theorem fusedMap2500swap_checked : acceptsGraphIso
    (fused (graph core2500) (root 10) 4 0) DegreeTwoThreeSpectrum5212.graph fusedMap2500swap=true := by decide +kernel
theorem certified2500swap : Certified (graph core2500) (root 10) 4 0 :=
  of_native_maps core2500 DegreeTwoThreeSpectrum5211.graph DegreeTwoThreeSpectrum5212.graph
    sourceMap2500swap fusedMap2500swap sourceMap2500swap_checked fusedMap2500swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2500
#print axioms sourceMap2500swap_checked
#print axioms fusedMap2500swap_checked
#print axioms certified2500swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

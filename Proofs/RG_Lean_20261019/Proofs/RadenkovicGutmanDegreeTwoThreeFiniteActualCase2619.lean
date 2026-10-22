/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2619 : Family 10 := level10.get ⟨594,by decide⟩
def sourceMap2619 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2619 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2619_checked : acceptsGraphIso
    (source (graph core2619) (root 10) 0 4) DegreeTwoThreeSpectrum6300.graph sourceMap2619=true := by decide +kernel
theorem fusedMap2619_checked : acceptsGraphIso
    (fused (graph core2619) (root 10) 0 4) DegreeTwoThreeSpectrum5268.graph fusedMap2619=true := by decide +kernel
theorem certified2619 : Certified (graph core2619) (root 10) 0 4 :=
  of_native_maps core2619 DegreeTwoThreeSpectrum6300.graph DegreeTwoThreeSpectrum5268.graph
    sourceMap2619 fusedMap2619 sourceMap2619_checked fusedMap2619_checked
    DegreeTwoThreeFiniteComparisons.comparison2619
#print axioms sourceMap2619_checked
#print axioms fusedMap2619_checked
#print axioms certified2619
def sourceMap2619swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2619swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2619swap_checked : acceptsGraphIso
    (source (graph core2619) (root 10) 4 0) DegreeTwoThreeSpectrum6300.graph sourceMap2619swap=true := by decide +kernel
theorem fusedMap2619swap_checked : acceptsGraphIso
    (fused (graph core2619) (root 10) 4 0) DegreeTwoThreeSpectrum5268.graph fusedMap2619swap=true := by decide +kernel
theorem certified2619swap : Certified (graph core2619) (root 10) 4 0 :=
  of_native_maps core2619 DegreeTwoThreeSpectrum6300.graph DegreeTwoThreeSpectrum5268.graph
    sourceMap2619swap fusedMap2619swap sourceMap2619swap_checked fusedMap2619swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2619
#print axioms sourceMap2619swap_checked
#print axioms fusedMap2619swap_checked
#print axioms certified2619swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

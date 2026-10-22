/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2506 : Family 10 := level10.get ⟨234,by decide⟩
def sourceMap2506 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2506 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2506_checked : acceptsGraphIso
    (source (graph core2506) (root 10) 0 4) DegreeTwoThreeSpectrum5292.graph sourceMap2506=true := by decide +kernel
theorem fusedMap2506_checked : acceptsGraphIso
    (fused (graph core2506) (root 10) 0 4) DegreeTwoThreeSpectrum5293.graph fusedMap2506=true := by decide +kernel
theorem certified2506 : Certified (graph core2506) (root 10) 0 4 :=
  of_native_maps core2506 DegreeTwoThreeSpectrum5292.graph DegreeTwoThreeSpectrum5293.graph
    sourceMap2506 fusedMap2506 sourceMap2506_checked fusedMap2506_checked
    DegreeTwoThreeFiniteComparisons.comparison2506
#print axioms sourceMap2506_checked
#print axioms fusedMap2506_checked
#print axioms certified2506
def sourceMap2506swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2506swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2506swap_checked : acceptsGraphIso
    (source (graph core2506) (root 10) 4 0) DegreeTwoThreeSpectrum5292.graph sourceMap2506swap=true := by decide +kernel
theorem fusedMap2506swap_checked : acceptsGraphIso
    (fused (graph core2506) (root 10) 4 0) DegreeTwoThreeSpectrum5293.graph fusedMap2506swap=true := by decide +kernel
theorem certified2506swap : Certified (graph core2506) (root 10) 4 0 :=
  of_native_maps core2506 DegreeTwoThreeSpectrum5292.graph DegreeTwoThreeSpectrum5293.graph
    sourceMap2506swap fusedMap2506swap sourceMap2506swap_checked fusedMap2506swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2506
#print axioms sourceMap2506swap_checked
#print axioms fusedMap2506swap_checked
#print axioms certified2506swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

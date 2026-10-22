/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2478 : Family 10 := level10.get ⟨130,by decide⟩
def sourceMap2478 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2478 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2478_checked : acceptsGraphIso
    (source (graph core2478) (root 10) 0 4) DegreeTwoThreeSpectrum5757.graph sourceMap2478=true := by decide +kernel
theorem fusedMap2478_checked : acceptsGraphIso
    (fused (graph core2478) (root 10) 0 4) DegreeTwoThreeSpectrum5059.graph fusedMap2478=true := by decide +kernel
theorem certified2478 : Certified (graph core2478) (root 10) 0 4 :=
  of_native_maps core2478 DegreeTwoThreeSpectrum5757.graph DegreeTwoThreeSpectrum5059.graph
    sourceMap2478 fusedMap2478 sourceMap2478_checked fusedMap2478_checked
    DegreeTwoThreeFiniteComparisons.comparison2478
#print axioms sourceMap2478_checked
#print axioms fusedMap2478_checked
#print axioms certified2478
def sourceMap2478swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2478swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2478swap_checked : acceptsGraphIso
    (source (graph core2478) (root 10) 4 0) DegreeTwoThreeSpectrum5757.graph sourceMap2478swap=true := by decide +kernel
theorem fusedMap2478swap_checked : acceptsGraphIso
    (fused (graph core2478) (root 10) 4 0) DegreeTwoThreeSpectrum5059.graph fusedMap2478swap=true := by decide +kernel
theorem certified2478swap : Certified (graph core2478) (root 10) 4 0 :=
  of_native_maps core2478 DegreeTwoThreeSpectrum5757.graph DegreeTwoThreeSpectrum5059.graph
    sourceMap2478swap fusedMap2478swap sourceMap2478swap_checked fusedMap2478swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2478
#print axioms sourceMap2478swap_checked
#print axioms fusedMap2478swap_checked
#print axioms certified2478swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

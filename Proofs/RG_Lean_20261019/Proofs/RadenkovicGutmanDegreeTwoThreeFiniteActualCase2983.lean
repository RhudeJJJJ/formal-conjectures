/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2983 : Family 10 := level10.get ⟨1529,by decide⟩
def sourceMap2983 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2983 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2983_checked : acceptsGraphIso
    (source (graph core2983) (root 10) 0 4) DegreeTwoThreeSpectrum7067.graph sourceMap2983=true := by decide +kernel
theorem fusedMap2983_checked : acceptsGraphIso
    (fused (graph core2983) (root 10) 0 4) DegreeTwoThreeSpectrum5966.graph fusedMap2983=true := by decide +kernel
theorem certified2983 : Certified (graph core2983) (root 10) 0 4 :=
  of_native_maps core2983 DegreeTwoThreeSpectrum7067.graph DegreeTwoThreeSpectrum5966.graph
    sourceMap2983 fusedMap2983 sourceMap2983_checked fusedMap2983_checked
    DegreeTwoThreeFiniteComparisons.comparison2983
#print axioms sourceMap2983_checked
#print axioms fusedMap2983_checked
#print axioms certified2983
def sourceMap2983swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2983swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2983swap_checked : acceptsGraphIso
    (source (graph core2983) (root 10) 4 0) DegreeTwoThreeSpectrum7067.graph sourceMap2983swap=true := by decide +kernel
theorem fusedMap2983swap_checked : acceptsGraphIso
    (fused (graph core2983) (root 10) 4 0) DegreeTwoThreeSpectrum5966.graph fusedMap2983swap=true := by decide +kernel
theorem certified2983swap : Certified (graph core2983) (root 10) 4 0 :=
  of_native_maps core2983 DegreeTwoThreeSpectrum7067.graph DegreeTwoThreeSpectrum5966.graph
    sourceMap2983swap fusedMap2983swap sourceMap2983swap_checked fusedMap2983swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2983
#print axioms sourceMap2983swap_checked
#print axioms fusedMap2983swap_checked
#print axioms certified2983swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

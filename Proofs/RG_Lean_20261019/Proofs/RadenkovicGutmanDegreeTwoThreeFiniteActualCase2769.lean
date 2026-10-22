/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2769 : Family 10 := level10.get ⟨984,by decide⟩
def sourceMap2769 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2769 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2769_checked : acceptsGraphIso
    (source (graph core2769) (root 10) 0 4) DegreeTwoThreeSpectrum7050.graph sourceMap2769=true := by decide +kernel
theorem fusedMap2769_checked : acceptsGraphIso
    (fused (graph core2769) (root 10) 0 4) DegreeTwoThreeSpectrum5920.graph fusedMap2769=true := by decide +kernel
theorem certified2769 : Certified (graph core2769) (root 10) 0 4 :=
  of_native_maps core2769 DegreeTwoThreeSpectrum7050.graph DegreeTwoThreeSpectrum5920.graph
    sourceMap2769 fusedMap2769 sourceMap2769_checked fusedMap2769_checked
    DegreeTwoThreeFiniteComparisons.comparison2769
#print axioms sourceMap2769_checked
#print axioms fusedMap2769_checked
#print axioms certified2769
def sourceMap2769swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2769swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2769swap_checked : acceptsGraphIso
    (source (graph core2769) (root 10) 4 0) DegreeTwoThreeSpectrum7050.graph sourceMap2769swap=true := by decide +kernel
theorem fusedMap2769swap_checked : acceptsGraphIso
    (fused (graph core2769) (root 10) 4 0) DegreeTwoThreeSpectrum5920.graph fusedMap2769swap=true := by decide +kernel
theorem certified2769swap : Certified (graph core2769) (root 10) 4 0 :=
  of_native_maps core2769 DegreeTwoThreeSpectrum7050.graph DegreeTwoThreeSpectrum5920.graph
    sourceMap2769swap fusedMap2769swap sourceMap2769swap_checked fusedMap2769swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2769
#print axioms sourceMap2769swap_checked
#print axioms fusedMap2769swap_checked
#print axioms certified2769swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2772 : Family 10 := level10.get ⟨1002,by decide⟩
def sourceMap2772 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2772 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2772_checked : acceptsGraphIso
    (source (graph core2772) (root 10) 0 4) DegreeTwoThreeSpectrum5980.graph sourceMap2772=true := by decide +kernel
theorem fusedMap2772_checked : acceptsGraphIso
    (fused (graph core2772) (root 10) 0 4) DegreeTwoThreeSpectrum5981.graph fusedMap2772=true := by decide +kernel
theorem certified2772 : Certified (graph core2772) (root 10) 0 4 :=
  of_native_maps core2772 DegreeTwoThreeSpectrum5980.graph DegreeTwoThreeSpectrum5981.graph
    sourceMap2772 fusedMap2772 sourceMap2772_checked fusedMap2772_checked
    DegreeTwoThreeFiniteComparisons.comparison2772
#print axioms sourceMap2772_checked
#print axioms fusedMap2772_checked
#print axioms certified2772
def sourceMap2772swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2772swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2772swap_checked : acceptsGraphIso
    (source (graph core2772) (root 10) 4 0) DegreeTwoThreeSpectrum5980.graph sourceMap2772swap=true := by decide +kernel
theorem fusedMap2772swap_checked : acceptsGraphIso
    (fused (graph core2772) (root 10) 4 0) DegreeTwoThreeSpectrum5981.graph fusedMap2772swap=true := by decide +kernel
theorem certified2772swap : Certified (graph core2772) (root 10) 4 0 :=
  of_native_maps core2772 DegreeTwoThreeSpectrum5980.graph DegreeTwoThreeSpectrum5981.graph
    sourceMap2772swap fusedMap2772swap sourceMap2772swap_checked fusedMap2772swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2772
#print axioms sourceMap2772swap_checked
#print axioms fusedMap2772swap_checked
#print axioms certified2772swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

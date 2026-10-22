/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2639 : Family 10 := level10.get ⟨649,by decide⟩
def sourceMap2639 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2639 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2639_checked : acceptsGraphIso
    (source (graph core2639) (root 10) 0 4) DegreeTwoThreeSpectrum6416.graph sourceMap2639=true := by decide +kernel
theorem fusedMap2639_checked : acceptsGraphIso
    (fused (graph core2639) (root 10) 0 4) DegreeTwoThreeSpectrum5351.graph fusedMap2639=true := by decide +kernel
theorem certified2639 : Certified (graph core2639) (root 10) 0 4 :=
  of_native_maps core2639 DegreeTwoThreeSpectrum6416.graph DegreeTwoThreeSpectrum5351.graph
    sourceMap2639 fusedMap2639 sourceMap2639_checked fusedMap2639_checked
    DegreeTwoThreeFiniteComparisons.comparison2639
#print axioms sourceMap2639_checked
#print axioms fusedMap2639_checked
#print axioms certified2639
def sourceMap2639swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2639swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2639swap_checked : acceptsGraphIso
    (source (graph core2639) (root 10) 4 0) DegreeTwoThreeSpectrum6416.graph sourceMap2639swap=true := by decide +kernel
theorem fusedMap2639swap_checked : acceptsGraphIso
    (fused (graph core2639) (root 10) 4 0) DegreeTwoThreeSpectrum5351.graph fusedMap2639swap=true := by decide +kernel
theorem certified2639swap : Certified (graph core2639) (root 10) 4 0 :=
  of_native_maps core2639 DegreeTwoThreeSpectrum6416.graph DegreeTwoThreeSpectrum5351.graph
    sourceMap2639swap fusedMap2639swap sourceMap2639swap_checked fusedMap2639swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2639
#print axioms sourceMap2639swap_checked
#print axioms fusedMap2639swap_checked
#print axioms certified2639swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

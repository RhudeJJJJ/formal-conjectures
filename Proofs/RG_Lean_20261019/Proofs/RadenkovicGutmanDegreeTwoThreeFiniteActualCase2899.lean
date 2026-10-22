/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2899 : Family 10 := level10.get ⟨1319,by decide⟩
def sourceMap2899 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2899 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2899_checked : acceptsGraphIso
    (source (graph core2899) (root 10) 0 4) DegreeTwoThreeSpectrum6625.graph sourceMap2899=true := by decide +kernel
theorem fusedMap2899_checked : acceptsGraphIso
    (fused (graph core2899) (root 10) 0 4) DegreeTwoThreeSpectrum6626.graph fusedMap2899=true := by decide +kernel
theorem certified2899 : Certified (graph core2899) (root 10) 0 4 :=
  of_native_maps core2899 DegreeTwoThreeSpectrum6625.graph DegreeTwoThreeSpectrum6626.graph
    sourceMap2899 fusedMap2899 sourceMap2899_checked fusedMap2899_checked
    DegreeTwoThreeFiniteComparisons.comparison2899
#print axioms sourceMap2899_checked
#print axioms fusedMap2899_checked
#print axioms certified2899
def sourceMap2899swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2899swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2899swap_checked : acceptsGraphIso
    (source (graph core2899) (root 10) 4 0) DegreeTwoThreeSpectrum6625.graph sourceMap2899swap=true := by decide +kernel
theorem fusedMap2899swap_checked : acceptsGraphIso
    (fused (graph core2899) (root 10) 4 0) DegreeTwoThreeSpectrum6626.graph fusedMap2899swap=true := by decide +kernel
theorem certified2899swap : Certified (graph core2899) (root 10) 4 0 :=
  of_native_maps core2899 DegreeTwoThreeSpectrum6625.graph DegreeTwoThreeSpectrum6626.graph
    sourceMap2899swap fusedMap2899swap sourceMap2899swap_checked fusedMap2899swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2899
#print axioms sourceMap2899swap_checked
#print axioms fusedMap2899swap_checked
#print axioms certified2899swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

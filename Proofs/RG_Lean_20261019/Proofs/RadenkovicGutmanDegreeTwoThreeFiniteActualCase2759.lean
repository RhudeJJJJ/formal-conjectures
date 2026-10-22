/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2759 : Family 10 := level10.get ⟨967,by decide⟩
def sourceMap2759 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2759 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2759_checked : acceptsGraphIso
    (source (graph core2759) (root 10) 0 4) DegreeTwoThreeSpectrum7037.graph sourceMap2759=true := by decide +kernel
theorem fusedMap2759_checked : acceptsGraphIso
    (fused (graph core2759) (root 10) 0 4) DegreeTwoThreeSpectrum5886.graph fusedMap2759=true := by decide +kernel
theorem certified2759 : Certified (graph core2759) (root 10) 0 4 :=
  of_native_maps core2759 DegreeTwoThreeSpectrum7037.graph DegreeTwoThreeSpectrum5886.graph
    sourceMap2759 fusedMap2759 sourceMap2759_checked fusedMap2759_checked
    DegreeTwoThreeFiniteComparisons.comparison2759
#print axioms sourceMap2759_checked
#print axioms fusedMap2759_checked
#print axioms certified2759
def sourceMap2759swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2759swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2759swap_checked : acceptsGraphIso
    (source (graph core2759) (root 10) 4 0) DegreeTwoThreeSpectrum7037.graph sourceMap2759swap=true := by decide +kernel
theorem fusedMap2759swap_checked : acceptsGraphIso
    (fused (graph core2759) (root 10) 4 0) DegreeTwoThreeSpectrum5886.graph fusedMap2759swap=true := by decide +kernel
theorem certified2759swap : Certified (graph core2759) (root 10) 4 0 :=
  of_native_maps core2759 DegreeTwoThreeSpectrum7037.graph DegreeTwoThreeSpectrum5886.graph
    sourceMap2759swap fusedMap2759swap sourceMap2759swap_checked fusedMap2759swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2759
#print axioms sourceMap2759swap_checked
#print axioms fusedMap2759swap_checked
#print axioms certified2759swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1965 : Family 10 := level10.get ⟨1539,by decide⟩
def sourceMap1965 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1965 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1965_checked : acceptsGraphIso
    (source (graph core1965) (root 10) 0 2) DegreeTwoThreeSpectrum3746.graph sourceMap1965=true := by decide +kernel
theorem fusedMap1965_checked : acceptsGraphIso
    (fused (graph core1965) (root 10) 0 2) DegreeTwoThreeSpectrum3013.graph fusedMap1965=true := by decide +kernel
theorem certified1965 : Certified (graph core1965) (root 10) 0 2 :=
  of_native_maps core1965 DegreeTwoThreeSpectrum3746.graph DegreeTwoThreeSpectrum3013.graph
    sourceMap1965 fusedMap1965 sourceMap1965_checked fusedMap1965_checked
    DegreeTwoThreeFiniteComparisons.comparison1965
#print axioms sourceMap1965_checked
#print axioms fusedMap1965_checked
#print axioms certified1965
def sourceMap1965swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1965swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1965swap_checked : acceptsGraphIso
    (source (graph core1965) (root 10) 2 0) DegreeTwoThreeSpectrum3746.graph sourceMap1965swap=true := by decide +kernel
theorem fusedMap1965swap_checked : acceptsGraphIso
    (fused (graph core1965) (root 10) 2 0) DegreeTwoThreeSpectrum3013.graph fusedMap1965swap=true := by decide +kernel
theorem certified1965swap : Certified (graph core1965) (root 10) 2 0 :=
  of_native_maps core1965 DegreeTwoThreeSpectrum3746.graph DegreeTwoThreeSpectrum3013.graph
    sourceMap1965swap fusedMap1965swap sourceMap1965swap_checked fusedMap1965swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1965
#print axioms sourceMap1965swap_checked
#print axioms fusedMap1965swap_checked
#print axioms certified1965swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

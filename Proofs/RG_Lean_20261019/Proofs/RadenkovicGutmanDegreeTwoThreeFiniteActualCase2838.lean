/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2838 : Family 10 := level10.get ⟨1168,by decide⟩
def sourceMap2838 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2838 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2838_checked : acceptsGraphIso
    (source (graph core2838) (root 10) 0 4) DegreeTwoThreeSpectrum6319.graph sourceMap2838=true := by decide +kernel
theorem fusedMap2838_checked : acceptsGraphIso
    (fused (graph core2838) (root 10) 0 4) DegreeTwoThreeSpectrum6320.graph fusedMap2838=true := by decide +kernel
theorem certified2838 : Certified (graph core2838) (root 10) 0 4 :=
  of_native_maps core2838 DegreeTwoThreeSpectrum6319.graph DegreeTwoThreeSpectrum6320.graph
    sourceMap2838 fusedMap2838 sourceMap2838_checked fusedMap2838_checked
    DegreeTwoThreeFiniteComparisons.comparison2838
#print axioms sourceMap2838_checked
#print axioms fusedMap2838_checked
#print axioms certified2838
def sourceMap2838swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2838swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2838swap_checked : acceptsGraphIso
    (source (graph core2838) (root 10) 4 0) DegreeTwoThreeSpectrum6319.graph sourceMap2838swap=true := by decide +kernel
theorem fusedMap2838swap_checked : acceptsGraphIso
    (fused (graph core2838) (root 10) 4 0) DegreeTwoThreeSpectrum6320.graph fusedMap2838swap=true := by decide +kernel
theorem certified2838swap : Certified (graph core2838) (root 10) 4 0 :=
  of_native_maps core2838 DegreeTwoThreeSpectrum6319.graph DegreeTwoThreeSpectrum6320.graph
    sourceMap2838swap fusedMap2838swap sourceMap2838swap_checked fusedMap2838swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2838
#print axioms sourceMap2838swap_checked
#print axioms fusedMap2838swap_checked
#print axioms certified2838swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

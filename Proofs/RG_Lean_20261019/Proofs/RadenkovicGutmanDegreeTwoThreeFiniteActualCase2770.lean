/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2770 : Family 10 := level10.get ⟨988,by decide⟩
def sourceMap2770 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2770 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2770_checked : acceptsGraphIso
    (source (graph core2770) (root 10) 0 4) DegreeTwoThreeSpectrum7054.graph sourceMap2770=true := by decide +kernel
theorem fusedMap2770_checked : acceptsGraphIso
    (fused (graph core2770) (root 10) 0 4) DegreeTwoThreeSpectrum5928.graph fusedMap2770=true := by decide +kernel
theorem certified2770 : Certified (graph core2770) (root 10) 0 4 :=
  of_native_maps core2770 DegreeTwoThreeSpectrum7054.graph DegreeTwoThreeSpectrum5928.graph
    sourceMap2770 fusedMap2770 sourceMap2770_checked fusedMap2770_checked
    DegreeTwoThreeFiniteComparisons.comparison2770
#print axioms sourceMap2770_checked
#print axioms fusedMap2770_checked
#print axioms certified2770
def sourceMap2770swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2770swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2770swap_checked : acceptsGraphIso
    (source (graph core2770) (root 10) 4 0) DegreeTwoThreeSpectrum7054.graph sourceMap2770swap=true := by decide +kernel
theorem fusedMap2770swap_checked : acceptsGraphIso
    (fused (graph core2770) (root 10) 4 0) DegreeTwoThreeSpectrum5928.graph fusedMap2770swap=true := by decide +kernel
theorem certified2770swap : Certified (graph core2770) (root 10) 4 0 :=
  of_native_maps core2770 DegreeTwoThreeSpectrum7054.graph DegreeTwoThreeSpectrum5928.graph
    sourceMap2770swap fusedMap2770swap sourceMap2770swap_checked fusedMap2770swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2770
#print axioms sourceMap2770swap_checked
#print axioms fusedMap2770swap_checked
#print axioms certified2770swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

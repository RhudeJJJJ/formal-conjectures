/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2776 : Family 10 := level10.get ⟨1014,by decide⟩
def sourceMap2776 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2776 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2776_checked : acceptsGraphIso
    (source (graph core2776) (root 10) 0 4) DegreeTwoThreeSpectrum6008.graph sourceMap2776=true := by decide +kernel
theorem fusedMap2776_checked : acceptsGraphIso
    (fused (graph core2776) (root 10) 0 4) DegreeTwoThreeSpectrum6009.graph fusedMap2776=true := by decide +kernel
theorem certified2776 : Certified (graph core2776) (root 10) 0 4 :=
  of_native_maps core2776 DegreeTwoThreeSpectrum6008.graph DegreeTwoThreeSpectrum6009.graph
    sourceMap2776 fusedMap2776 sourceMap2776_checked fusedMap2776_checked
    DegreeTwoThreeFiniteComparisons.comparison2776
#print axioms sourceMap2776_checked
#print axioms fusedMap2776_checked
#print axioms certified2776
def sourceMap2776swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2776swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2776swap_checked : acceptsGraphIso
    (source (graph core2776) (root 10) 4 0) DegreeTwoThreeSpectrum6008.graph sourceMap2776swap=true := by decide +kernel
theorem fusedMap2776swap_checked : acceptsGraphIso
    (fused (graph core2776) (root 10) 4 0) DegreeTwoThreeSpectrum6009.graph fusedMap2776swap=true := by decide +kernel
theorem certified2776swap : Certified (graph core2776) (root 10) 4 0 :=
  of_native_maps core2776 DegreeTwoThreeSpectrum6008.graph DegreeTwoThreeSpectrum6009.graph
    sourceMap2776swap fusedMap2776swap sourceMap2776swap_checked fusedMap2776swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2776
#print axioms sourceMap2776swap_checked
#print axioms fusedMap2776swap_checked
#print axioms certified2776swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3040 : Family 10 := level10.get ⟨1662,by decide⟩
def sourceMap3040 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3040 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3040_checked : acceptsGraphIso
    (source (graph core3040) (root 10) 0 4) DegreeTwoThreeSpectrum7228.graph sourceMap3040=true := by decide +kernel
theorem fusedMap3040_checked : acceptsGraphIso
    (fused (graph core3040) (root 10) 0 4) DegreeTwoThreeSpectrum6278.graph fusedMap3040=true := by decide +kernel
theorem certified3040 : Certified (graph core3040) (root 10) 0 4 :=
  of_native_maps core3040 DegreeTwoThreeSpectrum7228.graph DegreeTwoThreeSpectrum6278.graph
    sourceMap3040 fusedMap3040 sourceMap3040_checked fusedMap3040_checked
    DegreeTwoThreeFiniteComparisons.comparison3040
#print axioms sourceMap3040_checked
#print axioms fusedMap3040_checked
#print axioms certified3040
def sourceMap3040swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3040swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3040swap_checked : acceptsGraphIso
    (source (graph core3040) (root 10) 4 0) DegreeTwoThreeSpectrum7228.graph sourceMap3040swap=true := by decide +kernel
theorem fusedMap3040swap_checked : acceptsGraphIso
    (fused (graph core3040) (root 10) 4 0) DegreeTwoThreeSpectrum6278.graph fusedMap3040swap=true := by decide +kernel
theorem certified3040swap : Certified (graph core3040) (root 10) 4 0 :=
  of_native_maps core3040 DegreeTwoThreeSpectrum7228.graph DegreeTwoThreeSpectrum6278.graph
    sourceMap3040swap fusedMap3040swap sourceMap3040swap_checked fusedMap3040swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3040
#print axioms sourceMap3040swap_checked
#print axioms fusedMap3040swap_checked
#print axioms certified3040swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

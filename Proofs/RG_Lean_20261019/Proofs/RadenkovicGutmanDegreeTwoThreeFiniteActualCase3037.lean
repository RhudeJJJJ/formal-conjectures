/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3037 : Family 10 := level10.get ⟨1654,by decide⟩
def sourceMap3037 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3037 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3037_checked : acceptsGraphIso
    (source (graph core3037) (root 10) 0 4) DegreeTwoThreeSpectrum7215.graph sourceMap3037=true := by decide +kernel
theorem fusedMap3037_checked : acceptsGraphIso
    (fused (graph core3037) (root 10) 0 4) DegreeTwoThreeSpectrum6254.graph fusedMap3037=true := by decide +kernel
theorem certified3037 : Certified (graph core3037) (root 10) 0 4 :=
  of_native_maps core3037 DegreeTwoThreeSpectrum7215.graph DegreeTwoThreeSpectrum6254.graph
    sourceMap3037 fusedMap3037 sourceMap3037_checked fusedMap3037_checked
    DegreeTwoThreeFiniteComparisons.comparison3037
#print axioms sourceMap3037_checked
#print axioms fusedMap3037_checked
#print axioms certified3037
def sourceMap3037swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3037swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3037swap_checked : acceptsGraphIso
    (source (graph core3037) (root 10) 4 0) DegreeTwoThreeSpectrum7215.graph sourceMap3037swap=true := by decide +kernel
theorem fusedMap3037swap_checked : acceptsGraphIso
    (fused (graph core3037) (root 10) 4 0) DegreeTwoThreeSpectrum6254.graph fusedMap3037swap=true := by decide +kernel
theorem certified3037swap : Certified (graph core3037) (root 10) 4 0 :=
  of_native_maps core3037 DegreeTwoThreeSpectrum7215.graph DegreeTwoThreeSpectrum6254.graph
    sourceMap3037swap fusedMap3037swap sourceMap3037swap_checked fusedMap3037swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3037
#print axioms sourceMap3037swap_checked
#print axioms fusedMap3037swap_checked
#print axioms certified3037swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

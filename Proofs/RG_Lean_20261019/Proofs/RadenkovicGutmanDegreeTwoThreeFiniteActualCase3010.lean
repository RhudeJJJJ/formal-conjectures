/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3010 : Family 10 := level10.get ⟨1588,by decide⟩
def sourceMap3010 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3010 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3010_checked : acceptsGraphIso
    (source (graph core3010) (root 10) 0 4) DegreeTwoThreeSpectrum7126.graph sourceMap3010=true := by decide +kernel
theorem fusedMap3010_checked : acceptsGraphIso
    (fused (graph core3010) (root 10) 0 4) DegreeTwoThreeSpectrum6080.graph fusedMap3010=true := by decide +kernel
theorem certified3010 : Certified (graph core3010) (root 10) 0 4 :=
  of_native_maps core3010 DegreeTwoThreeSpectrum7126.graph DegreeTwoThreeSpectrum6080.graph
    sourceMap3010 fusedMap3010 sourceMap3010_checked fusedMap3010_checked
    DegreeTwoThreeFiniteComparisons.comparison3010
#print axioms sourceMap3010_checked
#print axioms fusedMap3010_checked
#print axioms certified3010
def sourceMap3010swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3010swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3010swap_checked : acceptsGraphIso
    (source (graph core3010) (root 10) 4 0) DegreeTwoThreeSpectrum7126.graph sourceMap3010swap=true := by decide +kernel
theorem fusedMap3010swap_checked : acceptsGraphIso
    (fused (graph core3010) (root 10) 4 0) DegreeTwoThreeSpectrum6080.graph fusedMap3010swap=true := by decide +kernel
theorem certified3010swap : Certified (graph core3010) (root 10) 4 0 :=
  of_native_maps core3010 DegreeTwoThreeSpectrum7126.graph DegreeTwoThreeSpectrum6080.graph
    sourceMap3010swap fusedMap3010swap sourceMap3010swap_checked fusedMap3010swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3010
#print axioms sourceMap3010swap_checked
#print axioms fusedMap3010swap_checked
#print axioms certified3010swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

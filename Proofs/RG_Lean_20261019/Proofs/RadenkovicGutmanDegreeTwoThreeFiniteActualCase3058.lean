/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3058 : Family 10 := level10.get ⟨1724,by decide⟩
def sourceMap3058 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3058 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3058_checked : acceptsGraphIso
    (source (graph core3058) (root 10) 0 4) DegreeTwoThreeSpectrum7351.graph sourceMap3058=true := by decide +kernel
theorem fusedMap3058_checked : acceptsGraphIso
    (fused (graph core3058) (root 10) 0 4) DegreeTwoThreeSpectrum6526.graph fusedMap3058=true := by decide +kernel
theorem certified3058 : Certified (graph core3058) (root 10) 0 4 :=
  of_native_maps core3058 DegreeTwoThreeSpectrum7351.graph DegreeTwoThreeSpectrum6526.graph
    sourceMap3058 fusedMap3058 sourceMap3058_checked fusedMap3058_checked
    DegreeTwoThreeFiniteComparisons.comparison3058
#print axioms sourceMap3058_checked
#print axioms fusedMap3058_checked
#print axioms certified3058
def sourceMap3058swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3058swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3058swap_checked : acceptsGraphIso
    (source (graph core3058) (root 10) 4 0) DegreeTwoThreeSpectrum7351.graph sourceMap3058swap=true := by decide +kernel
theorem fusedMap3058swap_checked : acceptsGraphIso
    (fused (graph core3058) (root 10) 4 0) DegreeTwoThreeSpectrum6526.graph fusedMap3058swap=true := by decide +kernel
theorem certified3058swap : Certified (graph core3058) (root 10) 4 0 :=
  of_native_maps core3058 DegreeTwoThreeSpectrum7351.graph DegreeTwoThreeSpectrum6526.graph
    sourceMap3058swap fusedMap3058swap sourceMap3058swap_checked fusedMap3058swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3058
#print axioms sourceMap3058swap_checked
#print axioms fusedMap3058swap_checked
#print axioms certified3058swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

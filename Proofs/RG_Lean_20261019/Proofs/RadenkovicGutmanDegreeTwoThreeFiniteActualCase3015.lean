/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3015 : Family 10 := level10.get ⟨1600,by decide⟩
def sourceMap3015 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3015 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3015_checked : acceptsGraphIso
    (source (graph core3015) (root 10) 0 4) DegreeTwoThreeSpectrum7144.graph sourceMap3015=true := by decide +kernel
theorem fusedMap3015_checked : acceptsGraphIso
    (fused (graph core3015) (root 10) 0 4) DegreeTwoThreeSpectrum6115.graph fusedMap3015=true := by decide +kernel
theorem certified3015 : Certified (graph core3015) (root 10) 0 4 :=
  of_native_maps core3015 DegreeTwoThreeSpectrum7144.graph DegreeTwoThreeSpectrum6115.graph
    sourceMap3015 fusedMap3015 sourceMap3015_checked fusedMap3015_checked
    DegreeTwoThreeFiniteComparisons.comparison3015
#print axioms sourceMap3015_checked
#print axioms fusedMap3015_checked
#print axioms certified3015
def sourceMap3015swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3015swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3015swap_checked : acceptsGraphIso
    (source (graph core3015) (root 10) 4 0) DegreeTwoThreeSpectrum7144.graph sourceMap3015swap=true := by decide +kernel
theorem fusedMap3015swap_checked : acceptsGraphIso
    (fused (graph core3015) (root 10) 4 0) DegreeTwoThreeSpectrum6115.graph fusedMap3015swap=true := by decide +kernel
theorem certified3015swap : Certified (graph core3015) (root 10) 4 0 :=
  of_native_maps core3015 DegreeTwoThreeSpectrum7144.graph DegreeTwoThreeSpectrum6115.graph
    sourceMap3015swap fusedMap3015swap sourceMap3015swap_checked fusedMap3015swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3015
#print axioms sourceMap3015swap_checked
#print axioms fusedMap3015swap_checked
#print axioms certified3015swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

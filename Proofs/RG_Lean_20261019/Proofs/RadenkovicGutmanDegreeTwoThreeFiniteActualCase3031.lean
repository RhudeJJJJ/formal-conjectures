/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3031 : Family 10 := level10.get ⟨1639,by decide⟩
def sourceMap3031 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3031 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3031_checked : acceptsGraphIso
    (source (graph core3031) (root 10) 0 4) DegreeTwoThreeSpectrum7195.graph sourceMap3031=true := by decide +kernel
theorem fusedMap3031_checked : acceptsGraphIso
    (fused (graph core3031) (root 10) 0 4) DegreeTwoThreeSpectrum6214.graph fusedMap3031=true := by decide +kernel
theorem certified3031 : Certified (graph core3031) (root 10) 0 4 :=
  of_native_maps core3031 DegreeTwoThreeSpectrum7195.graph DegreeTwoThreeSpectrum6214.graph
    sourceMap3031 fusedMap3031 sourceMap3031_checked fusedMap3031_checked
    DegreeTwoThreeFiniteComparisons.comparison3031
#print axioms sourceMap3031_checked
#print axioms fusedMap3031_checked
#print axioms certified3031
def sourceMap3031swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3031swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3031swap_checked : acceptsGraphIso
    (source (graph core3031) (root 10) 4 0) DegreeTwoThreeSpectrum7195.graph sourceMap3031swap=true := by decide +kernel
theorem fusedMap3031swap_checked : acceptsGraphIso
    (fused (graph core3031) (root 10) 4 0) DegreeTwoThreeSpectrum6214.graph fusedMap3031swap=true := by decide +kernel
theorem certified3031swap : Certified (graph core3031) (root 10) 4 0 :=
  of_native_maps core3031 DegreeTwoThreeSpectrum7195.graph DegreeTwoThreeSpectrum6214.graph
    sourceMap3031swap fusedMap3031swap sourceMap3031swap_checked fusedMap3031swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3031
#print axioms sourceMap3031swap_checked
#print axioms fusedMap3031swap_checked
#print axioms certified3031swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

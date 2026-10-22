/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3011 : Family 10 := level10.get ⟨1591,by decide⟩
def sourceMap3011 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3011 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3011_checked : acceptsGraphIso
    (source (graph core3011) (root 10) 0 4) DegreeTwoThreeSpectrum7130.graph sourceMap3011=true := by decide +kernel
theorem fusedMap3011_checked : acceptsGraphIso
    (fused (graph core3011) (root 10) 0 4) DegreeTwoThreeSpectrum6090.graph fusedMap3011=true := by decide +kernel
theorem certified3011 : Certified (graph core3011) (root 10) 0 4 :=
  of_native_maps core3011 DegreeTwoThreeSpectrum7130.graph DegreeTwoThreeSpectrum6090.graph
    sourceMap3011 fusedMap3011 sourceMap3011_checked fusedMap3011_checked
    DegreeTwoThreeFiniteComparisons.comparison3011
#print axioms sourceMap3011_checked
#print axioms fusedMap3011_checked
#print axioms certified3011
def sourceMap3011swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3011swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3011swap_checked : acceptsGraphIso
    (source (graph core3011) (root 10) 4 0) DegreeTwoThreeSpectrum7130.graph sourceMap3011swap=true := by decide +kernel
theorem fusedMap3011swap_checked : acceptsGraphIso
    (fused (graph core3011) (root 10) 4 0) DegreeTwoThreeSpectrum6090.graph fusedMap3011swap=true := by decide +kernel
theorem certified3011swap : Certified (graph core3011) (root 10) 4 0 :=
  of_native_maps core3011 DegreeTwoThreeSpectrum7130.graph DegreeTwoThreeSpectrum6090.graph
    sourceMap3011swap fusedMap3011swap sourceMap3011swap_checked fusedMap3011swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3011
#print axioms sourceMap3011swap_checked
#print axioms fusedMap3011swap_checked
#print axioms certified3011swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

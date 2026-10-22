/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3027 : Family 10 := level10.get ⟨1632,by decide⟩
def sourceMap3027 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3027 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3027_checked : acceptsGraphIso
    (source (graph core3027) (root 10) 0 4) DegreeTwoThreeSpectrum7187.graph sourceMap3027=true := by decide +kernel
theorem fusedMap3027_checked : acceptsGraphIso
    (fused (graph core3027) (root 10) 0 4) DegreeTwoThreeSpectrum6197.graph fusedMap3027=true := by decide +kernel
theorem certified3027 : Certified (graph core3027) (root 10) 0 4 :=
  of_native_maps core3027 DegreeTwoThreeSpectrum7187.graph DegreeTwoThreeSpectrum6197.graph
    sourceMap3027 fusedMap3027 sourceMap3027_checked fusedMap3027_checked
    DegreeTwoThreeFiniteComparisons.comparison3027
#print axioms sourceMap3027_checked
#print axioms fusedMap3027_checked
#print axioms certified3027
def sourceMap3027swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3027swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3027swap_checked : acceptsGraphIso
    (source (graph core3027) (root 10) 4 0) DegreeTwoThreeSpectrum7187.graph sourceMap3027swap=true := by decide +kernel
theorem fusedMap3027swap_checked : acceptsGraphIso
    (fused (graph core3027) (root 10) 4 0) DegreeTwoThreeSpectrum6197.graph fusedMap3027swap=true := by decide +kernel
theorem certified3027swap : Certified (graph core3027) (root 10) 4 0 :=
  of_native_maps core3027 DegreeTwoThreeSpectrum7187.graph DegreeTwoThreeSpectrum6197.graph
    sourceMap3027swap fusedMap3027swap sourceMap3027swap_checked fusedMap3027swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3027
#print axioms sourceMap3027swap_checked
#print axioms fusedMap3027swap_checked
#print axioms certified3027swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

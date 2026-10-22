/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3513 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap3513 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3513 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3513_checked : acceptsGraphIso
    (source (graph core3513) (root 7) 0 6) DegreeTwoThreeSpectrum4010.graph sourceMap3513=true := by decide +kernel
theorem fusedMap3513_checked : acceptsGraphIso
    (fused (graph core3513) (root 7) 0 6) DegreeTwoThreeSpectrum4012.graph fusedMap3513=true := by decide +kernel
theorem certified3513 : Certified (graph core3513) (root 7) 0 6 :=
  of_native_maps core3513 DegreeTwoThreeSpectrum4010.graph DegreeTwoThreeSpectrum4012.graph
    sourceMap3513 fusedMap3513 sourceMap3513_checked fusedMap3513_checked
    DegreeTwoThreeFiniteComparisons.comparison3513
#print axioms sourceMap3513_checked
#print axioms fusedMap3513_checked
#print axioms certified3513
def sourceMap3513swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3513swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3513swap_checked : acceptsGraphIso
    (source (graph core3513) (root 7) 6 0) DegreeTwoThreeSpectrum4010.graph sourceMap3513swap=true := by decide +kernel
theorem fusedMap3513swap_checked : acceptsGraphIso
    (fused (graph core3513) (root 7) 6 0) DegreeTwoThreeSpectrum4012.graph fusedMap3513swap=true := by decide +kernel
theorem certified3513swap : Certified (graph core3513) (root 7) 6 0 :=
  of_native_maps core3513 DegreeTwoThreeSpectrum4010.graph DegreeTwoThreeSpectrum4012.graph
    sourceMap3513swap fusedMap3513swap sourceMap3513swap_checked fusedMap3513swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3513
#print axioms sourceMap3513swap_checked
#print axioms fusedMap3513swap_checked
#print axioms certified3513swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

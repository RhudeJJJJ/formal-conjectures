/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2997 : Family 10 := level10.get ⟨1559,by decide⟩
def sourceMap2997 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2997 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2997_checked : acceptsGraphIso
    (source (graph core2997) (root 10) 0 4) DegreeTwoThreeSpectrum7097.graph sourceMap2997=true := by decide +kernel
theorem fusedMap2997_checked : acceptsGraphIso
    (fused (graph core2997) (root 10) 0 4) DegreeTwoThreeSpectrum6022.graph fusedMap2997=true := by decide +kernel
theorem certified2997 : Certified (graph core2997) (root 10) 0 4 :=
  of_native_maps core2997 DegreeTwoThreeSpectrum7097.graph DegreeTwoThreeSpectrum6022.graph
    sourceMap2997 fusedMap2997 sourceMap2997_checked fusedMap2997_checked
    DegreeTwoThreeFiniteComparisons.comparison2997
#print axioms sourceMap2997_checked
#print axioms fusedMap2997_checked
#print axioms certified2997
def sourceMap2997swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2997swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2997swap_checked : acceptsGraphIso
    (source (graph core2997) (root 10) 4 0) DegreeTwoThreeSpectrum7097.graph sourceMap2997swap=true := by decide +kernel
theorem fusedMap2997swap_checked : acceptsGraphIso
    (fused (graph core2997) (root 10) 4 0) DegreeTwoThreeSpectrum6022.graph fusedMap2997swap=true := by decide +kernel
theorem certified2997swap : Certified (graph core2997) (root 10) 4 0 :=
  of_native_maps core2997 DegreeTwoThreeSpectrum7097.graph DegreeTwoThreeSpectrum6022.graph
    sourceMap2997swap fusedMap2997swap sourceMap2997swap_checked fusedMap2997swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2997
#print axioms sourceMap2997swap_checked
#print axioms fusedMap2997swap_checked
#print axioms certified2997swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2988 : Family 10 := level10.get ⟨1539,by decide⟩
def sourceMap2988 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2988 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2988_checked : acceptsGraphIso
    (source (graph core2988) (root 10) 0 4) DegreeTwoThreeSpectrum7077.graph sourceMap2988=true := by decide +kernel
theorem fusedMap2988_checked : acceptsGraphIso
    (fused (graph core2988) (root 10) 0 4) DegreeTwoThreeSpectrum5983.graph fusedMap2988=true := by decide +kernel
theorem certified2988 : Certified (graph core2988) (root 10) 0 4 :=
  of_native_maps core2988 DegreeTwoThreeSpectrum7077.graph DegreeTwoThreeSpectrum5983.graph
    sourceMap2988 fusedMap2988 sourceMap2988_checked fusedMap2988_checked
    DegreeTwoThreeFiniteComparisons.comparison2988
#print axioms sourceMap2988_checked
#print axioms fusedMap2988_checked
#print axioms certified2988
def sourceMap2988swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2988swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2988swap_checked : acceptsGraphIso
    (source (graph core2988) (root 10) 4 0) DegreeTwoThreeSpectrum7077.graph sourceMap2988swap=true := by decide +kernel
theorem fusedMap2988swap_checked : acceptsGraphIso
    (fused (graph core2988) (root 10) 4 0) DegreeTwoThreeSpectrum5983.graph fusedMap2988swap=true := by decide +kernel
theorem certified2988swap : Certified (graph core2988) (root 10) 4 0 :=
  of_native_maps core2988 DegreeTwoThreeSpectrum7077.graph DegreeTwoThreeSpectrum5983.graph
    sourceMap2988swap fusedMap2988swap sourceMap2988swap_checked fusedMap2988swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2988
#print axioms sourceMap2988swap_checked
#print axioms fusedMap2988swap_checked
#print axioms certified2988swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

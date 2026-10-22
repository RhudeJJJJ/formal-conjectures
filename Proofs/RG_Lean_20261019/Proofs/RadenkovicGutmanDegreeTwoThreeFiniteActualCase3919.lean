/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3919 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap3919 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3919 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3919_checked : acceptsGraphIso
    (source (graph core3919) (root 8) 1 4) DegreeTwoThreeSpectrum4666.graph sourceMap3919=true := by decide +kernel
theorem fusedMap3919_checked : acceptsGraphIso
    (fused (graph core3919) (root 8) 1 4) DegreeTwoThreeSpectrum4171.graph fusedMap3919=true := by decide +kernel
theorem certified3919 : Certified (graph core3919) (root 8) 1 4 :=
  of_native_maps core3919 DegreeTwoThreeSpectrum4666.graph DegreeTwoThreeSpectrum4171.graph
    sourceMap3919 fusedMap3919 sourceMap3919_checked fusedMap3919_checked
    DegreeTwoThreeFiniteComparisons.comparison3919
#print axioms sourceMap3919_checked
#print axioms fusedMap3919_checked
#print axioms certified3919
def sourceMap3919swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3919swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3919swap_checked : acceptsGraphIso
    (source (graph core3919) (root 8) 4 1) DegreeTwoThreeSpectrum4666.graph sourceMap3919swap=true := by decide +kernel
theorem fusedMap3919swap_checked : acceptsGraphIso
    (fused (graph core3919) (root 8) 4 1) DegreeTwoThreeSpectrum4171.graph fusedMap3919swap=true := by decide +kernel
theorem certified3919swap : Certified (graph core3919) (root 8) 4 1 :=
  of_native_maps core3919 DegreeTwoThreeSpectrum4666.graph DegreeTwoThreeSpectrum4171.graph
    sourceMap3919swap fusedMap3919swap sourceMap3919swap_checked fusedMap3919swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3919
#print axioms sourceMap3919swap_checked
#print axioms fusedMap3919swap_checked
#print axioms certified3919swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3878 : Family 8 := level8.get ⟨165,by decide⟩
def sourceMap3878 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3878 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3878_checked : acceptsGraphIso
    (source (graph core3878) (root 8) 1 4) DegreeTwoThreeSpectrum4573.graph sourceMap3878=true := by decide +kernel
theorem fusedMap3878_checked : acceptsGraphIso
    (fused (graph core3878) (root 8) 1 4) DegreeTwoThreeSpectrum4065.graph fusedMap3878=true := by decide +kernel
theorem certified3878 : Certified (graph core3878) (root 8) 1 4 :=
  of_native_maps core3878 DegreeTwoThreeSpectrum4573.graph DegreeTwoThreeSpectrum4065.graph
    sourceMap3878 fusedMap3878 sourceMap3878_checked fusedMap3878_checked
    DegreeTwoThreeFiniteComparisons.comparison3878
#print axioms sourceMap3878_checked
#print axioms fusedMap3878_checked
#print axioms certified3878
def sourceMap3878swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3878swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3878swap_checked : acceptsGraphIso
    (source (graph core3878) (root 8) 4 1) DegreeTwoThreeSpectrum4573.graph sourceMap3878swap=true := by decide +kernel
theorem fusedMap3878swap_checked : acceptsGraphIso
    (fused (graph core3878) (root 8) 4 1) DegreeTwoThreeSpectrum4065.graph fusedMap3878swap=true := by decide +kernel
theorem certified3878swap : Certified (graph core3878) (root 8) 4 1 :=
  of_native_maps core3878 DegreeTwoThreeSpectrum4573.graph DegreeTwoThreeSpectrum4065.graph
    sourceMap3878swap fusedMap3878swap sourceMap3878swap_checked fusedMap3878swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3878
#print axioms sourceMap3878swap_checked
#print axioms fusedMap3878swap_checked
#print axioms certified3878swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

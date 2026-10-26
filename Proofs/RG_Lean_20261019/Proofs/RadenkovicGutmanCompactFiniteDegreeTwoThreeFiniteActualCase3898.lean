/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3898 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap3898 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3898 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3898_checked : acceptsGraphIso
    (source (graph core3898) (root 8) 1 4) DegreeTwoThreeSpectrum4727.graph sourceMap3898=true := by decide +kernel
theorem fusedMap3898_checked : acceptsGraphIso
    (fused (graph core3898) (root 8) 1 4) DegreeTwoThreeSpectrum4272.graph fusedMap3898=true := by decide +kernel
theorem certified3898 : Certified (graph core3898) (root 8) 1 4 :=
  of_native_maps core3898 DegreeTwoThreeSpectrum4727.graph DegreeTwoThreeSpectrum4272.graph
    sourceMap3898 fusedMap3898 sourceMap3898_checked fusedMap3898_checked
    DegreeTwoThreeFiniteComparisons.comparison3898
#print axioms sourceMap3898_checked
#print axioms fusedMap3898_checked
#print axioms certified3898
def sourceMap3898swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3898swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3898swap_checked : acceptsGraphIso
    (source (graph core3898) (root 8) 4 1) DegreeTwoThreeSpectrum4727.graph sourceMap3898swap=true := by decide +kernel
theorem fusedMap3898swap_checked : acceptsGraphIso
    (fused (graph core3898) (root 8) 4 1) DegreeTwoThreeSpectrum4272.graph fusedMap3898swap=true := by decide +kernel
theorem certified3898swap : Certified (graph core3898) (root 8) 4 1 :=
  of_native_maps core3898 DegreeTwoThreeSpectrum4727.graph DegreeTwoThreeSpectrum4272.graph
    sourceMap3898swap fusedMap3898swap sourceMap3898swap_checked fusedMap3898swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3898
#print axioms sourceMap3898swap_checked
#print axioms fusedMap3898swap_checked
#print axioms certified3898swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

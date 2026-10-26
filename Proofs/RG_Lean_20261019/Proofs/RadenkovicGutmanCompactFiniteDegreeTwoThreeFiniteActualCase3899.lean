/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3899 : Family 8 := level8.get ⟨212,by decide⟩
def sourceMap3899 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3899 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3899_checked : acceptsGraphIso
    (source (graph core3899) (root 8) 1 4) DegreeTwoThreeSpectrum4731.graph sourceMap3899=true := by decide +kernel
theorem fusedMap3899_checked : acceptsGraphIso
    (fused (graph core3899) (root 8) 1 4) DegreeTwoThreeSpectrum4278.graph fusedMap3899=true := by decide +kernel
theorem certified3899 : Certified (graph core3899) (root 8) 1 4 :=
  of_native_maps core3899 DegreeTwoThreeSpectrum4731.graph DegreeTwoThreeSpectrum4278.graph
    sourceMap3899 fusedMap3899 sourceMap3899_checked fusedMap3899_checked
    DegreeTwoThreeFiniteComparisons.comparison3899
#print axioms sourceMap3899_checked
#print axioms fusedMap3899_checked
#print axioms certified3899
def sourceMap3899swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3899swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3899swap_checked : acceptsGraphIso
    (source (graph core3899) (root 8) 4 1) DegreeTwoThreeSpectrum4731.graph sourceMap3899swap=true := by decide +kernel
theorem fusedMap3899swap_checked : acceptsGraphIso
    (fused (graph core3899) (root 8) 4 1) DegreeTwoThreeSpectrum4278.graph fusedMap3899swap=true := by decide +kernel
theorem certified3899swap : Certified (graph core3899) (root 8) 4 1 :=
  of_native_maps core3899 DegreeTwoThreeSpectrum4731.graph DegreeTwoThreeSpectrum4278.graph
    sourceMap3899swap fusedMap3899swap sourceMap3899swap_checked fusedMap3899swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3899
#print axioms sourceMap3899swap_checked
#print axioms fusedMap3899swap_checked
#print axioms certified3899swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

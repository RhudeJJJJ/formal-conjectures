/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3799 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap3799 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3799 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3799_checked : acceptsGraphIso
    (source (graph core3799) (root 7) 1 4) DegreeTwoThreeSpectrum2609.graph sourceMap3799=true := by decide +kernel
theorem fusedMap3799_checked : acceptsGraphIso
    (fused (graph core3799) (root 7) 1 4) DegreeTwoThreeSpectrum2334.graph fusedMap3799=true := by decide +kernel
theorem certified3799 : Certified (graph core3799) (root 7) 1 4 :=
  of_native_maps core3799 DegreeTwoThreeSpectrum2609.graph DegreeTwoThreeSpectrum2334.graph
    sourceMap3799 fusedMap3799 sourceMap3799_checked fusedMap3799_checked
    DegreeTwoThreeFiniteComparisons.comparison3799
#print axioms sourceMap3799_checked
#print axioms fusedMap3799_checked
#print axioms certified3799
def sourceMap3799swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3799swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3799swap_checked : acceptsGraphIso
    (source (graph core3799) (root 7) 4 1) DegreeTwoThreeSpectrum2609.graph sourceMap3799swap=true := by decide +kernel
theorem fusedMap3799swap_checked : acceptsGraphIso
    (fused (graph core3799) (root 7) 4 1) DegreeTwoThreeSpectrum2334.graph fusedMap3799swap=true := by decide +kernel
theorem certified3799swap : Certified (graph core3799) (root 7) 4 1 :=
  of_native_maps core3799 DegreeTwoThreeSpectrum2609.graph DegreeTwoThreeSpectrum2334.graph
    sourceMap3799swap fusedMap3799swap sourceMap3799swap_checked fusedMap3799swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3799
#print axioms sourceMap3799swap_checked
#print axioms fusedMap3799swap_checked
#print axioms certified3799swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

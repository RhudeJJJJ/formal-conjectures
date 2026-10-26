/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3697 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap3697 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3697 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3697_checked : acceptsGraphIso
    (source (graph core3697) (root 7) 0 7) DegreeTwoThreeSpectrum5998.graph sourceMap3697=true := by decide +kernel
theorem fusedMap3697_checked : acceptsGraphIso
    (fused (graph core3697) (root 7) 0 7) DegreeTwoThreeSpectrum5139.graph fusedMap3697=true := by decide +kernel
theorem certified3697 : Certified (graph core3697) (root 7) 0 7 :=
  of_native_maps core3697 DegreeTwoThreeSpectrum5998.graph DegreeTwoThreeSpectrum5139.graph
    sourceMap3697 fusedMap3697 sourceMap3697_checked fusedMap3697_checked
    DegreeTwoThreeFiniteComparisons.comparison3697
#print axioms sourceMap3697_checked
#print axioms fusedMap3697_checked
#print axioms certified3697
def sourceMap3697swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,12,13,14,15,16,11] (sourceLabel 7 7 0 v)
def fusedMap3697swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3697swap_checked : acceptsGraphIso
    (source (graph core3697) (root 7) 7 0) DegreeTwoThreeSpectrum5998.graph sourceMap3697swap=true := by decide +kernel
theorem fusedMap3697swap_checked : acceptsGraphIso
    (fused (graph core3697) (root 7) 7 0) DegreeTwoThreeSpectrum5139.graph fusedMap3697swap=true := by decide +kernel
theorem certified3697swap : Certified (graph core3697) (root 7) 7 0 :=
  of_native_maps core3697 DegreeTwoThreeSpectrum5998.graph DegreeTwoThreeSpectrum5139.graph
    sourceMap3697swap fusedMap3697swap sourceMap3697swap_checked fusedMap3697swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3697
#print axioms sourceMap3697swap_checked
#print axioms fusedMap3697swap_checked
#print axioms certified3697swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

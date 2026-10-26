/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3643 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3643 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (sourceLabel 5 0 7 v)
def fusedMap3643 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 0 7 v)
theorem sourceMap3643_checked : acceptsGraphIso
    (source (graph core3643) (root 5) 0 7) DegreeTwoThreeSpectrum2383.graph sourceMap3643=true := by decide +kernel
theorem fusedMap3643_checked : acceptsGraphIso
    (fused (graph core3643) (root 5) 0 7) DegreeTwoThreeSpectrum2387.graph fusedMap3643=true := by decide +kernel
theorem certified3643 : Certified (graph core3643) (root 5) 0 7 :=
  of_native_maps core3643 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap3643 fusedMap3643 sourceMap3643_checked fusedMap3643_checked
    DegreeTwoThreeFiniteComparisons.comparison3643
#print axioms sourceMap3643_checked
#print axioms fusedMap3643_checked
#print axioms certified3643
def sourceMap3643swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,14,8] (sourceLabel 5 7 0 v)
def fusedMap3643swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 7 0 v)
theorem sourceMap3643swap_checked : acceptsGraphIso
    (source (graph core3643) (root 5) 7 0) DegreeTwoThreeSpectrum2383.graph sourceMap3643swap=true := by decide +kernel
theorem fusedMap3643swap_checked : acceptsGraphIso
    (fused (graph core3643) (root 5) 7 0) DegreeTwoThreeSpectrum2387.graph fusedMap3643swap=true := by decide +kernel
theorem certified3643swap : Certified (graph core3643) (root 5) 7 0 :=
  of_native_maps core3643 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap3643swap fusedMap3643swap sourceMap3643swap_checked fusedMap3643swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3643
#print axioms sourceMap3643swap_checked
#print axioms fusedMap3643swap_checked
#print axioms certified3643swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

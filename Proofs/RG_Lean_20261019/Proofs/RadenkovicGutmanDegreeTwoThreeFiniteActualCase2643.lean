/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2643 : Family 10 := level10.get ⟨663,by decide⟩
def sourceMap2643 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2643 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2643_checked : acceptsGraphIso
    (source (graph core2643) (root 10) 0 4) DegreeTwoThreeSpectrum6443.graph sourceMap2643=true := by decide +kernel
theorem fusedMap2643_checked : acceptsGraphIso
    (fused (graph core2643) (root 10) 0 4) DegreeTwoThreeSpectrum5372.graph fusedMap2643=true := by decide +kernel
theorem certified2643 : Certified (graph core2643) (root 10) 0 4 :=
  of_native_maps core2643 DegreeTwoThreeSpectrum6443.graph DegreeTwoThreeSpectrum5372.graph
    sourceMap2643 fusedMap2643 sourceMap2643_checked fusedMap2643_checked
    DegreeTwoThreeFiniteComparisons.comparison2643
#print axioms sourceMap2643_checked
#print axioms fusedMap2643_checked
#print axioms certified2643
def sourceMap2643swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2643swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2643swap_checked : acceptsGraphIso
    (source (graph core2643) (root 10) 4 0) DegreeTwoThreeSpectrum6443.graph sourceMap2643swap=true := by decide +kernel
theorem fusedMap2643swap_checked : acceptsGraphIso
    (fused (graph core2643) (root 10) 4 0) DegreeTwoThreeSpectrum5372.graph fusedMap2643swap=true := by decide +kernel
theorem certified2643swap : Certified (graph core2643) (root 10) 4 0 :=
  of_native_maps core2643 DegreeTwoThreeSpectrum6443.graph DegreeTwoThreeSpectrum5372.graph
    sourceMap2643swap fusedMap2643swap sourceMap2643swap_checked fusedMap2643swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2643
#print axioms sourceMap2643swap_checked
#print axioms fusedMap2643swap_checked
#print axioms certified2643swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

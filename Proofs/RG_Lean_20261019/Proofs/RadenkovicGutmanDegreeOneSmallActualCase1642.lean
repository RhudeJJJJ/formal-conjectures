/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1642 : Family 9 := level9.get ⟨387,by decide⟩
def sourceMap1642 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (sourceLabel 9 0 1 v)
def fusedMap1642 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1642_checked : acceptsGraphIso
    (source (graph core1642) (root 9) 0 1) DegreeOneSmallSpectrum1869.graph sourceMap1642=true := by decide +kernel
theorem fusedMap1642_checked : acceptsGraphIso
    (fused (graph core1642) (root 9) 0 1) DegreeOneSmallSpectrum1184.graph fusedMap1642=true := by decide +kernel
theorem certified1642 : Certified (graph core1642) (root 9) 0 1 :=
  of_native_maps core1642 DegreeOneSmallSpectrum1869.graph DegreeOneSmallSpectrum1184.graph
    sourceMap1642 fusedMap1642 sourceMap1642_checked fusedMap1642_checked
    DegreeOneSmallComparisons.comparison1642
#print axioms sourceMap1642_checked
#print axioms fusedMap1642_checked
#print axioms certified1642
def sourceMap1642swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 9 1 0 v)
def fusedMap1642swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1642swap_checked : acceptsGraphIso
    (source (graph core1642) (root 9) 1 0) DegreeOneSmallSpectrum1869.graph sourceMap1642swap=true := by decide +kernel
theorem fusedMap1642swap_checked : acceptsGraphIso
    (fused (graph core1642) (root 9) 1 0) DegreeOneSmallSpectrum1184.graph fusedMap1642swap=true := by decide +kernel
theorem certified1642swap : Certified (graph core1642) (root 9) 1 0 :=
  of_native_maps core1642 DegreeOneSmallSpectrum1869.graph DegreeOneSmallSpectrum1184.graph
    sourceMap1642swap fusedMap1642swap sourceMap1642swap_checked fusedMap1642swap_checked
    DegreeOneSmallComparisons.comparison1642
#print axioms sourceMap1642swap_checked
#print axioms fusedMap1642swap_checked
#print axioms certified1642swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

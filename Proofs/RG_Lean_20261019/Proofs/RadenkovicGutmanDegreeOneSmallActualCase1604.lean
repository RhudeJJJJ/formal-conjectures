/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1604 : Family 9 := level9.get ⟨343,by decide⟩
def sourceMap1604 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1604 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1604_checked : acceptsGraphIso
    (source (graph core1604) (root 9) 0 1) DegreeOneSmallSpectrum1688.graph sourceMap1604=true := by decide +kernel
theorem fusedMap1604_checked : acceptsGraphIso
    (fused (graph core1604) (root 9) 0 1) DegreeOneSmallSpectrum1039.graph fusedMap1604=true := by decide +kernel
theorem certified1604 : Certified (graph core1604) (root 9) 0 1 :=
  of_native_maps core1604 DegreeOneSmallSpectrum1688.graph DegreeOneSmallSpectrum1039.graph
    sourceMap1604 fusedMap1604 sourceMap1604_checked fusedMap1604_checked
    DegreeOneSmallComparisons.comparison1604
#print axioms sourceMap1604_checked
#print axioms fusedMap1604_checked
#print axioms certified1604
def sourceMap1604swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1604swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1604swap_checked : acceptsGraphIso
    (source (graph core1604) (root 9) 1 0) DegreeOneSmallSpectrum1688.graph sourceMap1604swap=true := by decide +kernel
theorem fusedMap1604swap_checked : acceptsGraphIso
    (fused (graph core1604) (root 9) 1 0) DegreeOneSmallSpectrum1039.graph fusedMap1604swap=true := by decide +kernel
theorem certified1604swap : Certified (graph core1604) (root 9) 1 0 :=
  of_native_maps core1604 DegreeOneSmallSpectrum1688.graph DegreeOneSmallSpectrum1039.graph
    sourceMap1604swap fusedMap1604swap sourceMap1604swap_checked fusedMap1604swap_checked
    DegreeOneSmallComparisons.comparison1604
#print axioms sourceMap1604swap_checked
#print axioms fusedMap1604swap_checked
#print axioms certified1604swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

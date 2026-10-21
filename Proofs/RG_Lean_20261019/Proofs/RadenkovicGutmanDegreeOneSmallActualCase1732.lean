/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1732 : Family 9 := level9.get ⟨550,by decide⟩
def sourceMap1732 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1732 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1732_checked : acceptsGraphIso
    (source (graph core1732) (root 9) 0 1) DegreeOneSmallSpectrum1557.graph sourceMap1732=true := by decide +kernel
theorem fusedMap1732_checked : acceptsGraphIso
    (fused (graph core1732) (root 9) 0 1) DegreeOneSmallSpectrum1558.graph fusedMap1732=true := by decide +kernel
theorem certified1732 : Certified (graph core1732) (root 9) 0 1 :=
  of_native_maps core1732 DegreeOneSmallSpectrum1557.graph DegreeOneSmallSpectrum1558.graph
    sourceMap1732 fusedMap1732 sourceMap1732_checked fusedMap1732_checked
    DegreeOneSmallComparisons.comparison1732
#print axioms sourceMap1732_checked
#print axioms fusedMap1732_checked
#print axioms certified1732
def sourceMap1732swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1732swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1732swap_checked : acceptsGraphIso
    (source (graph core1732) (root 9) 1 0) DegreeOneSmallSpectrum1557.graph sourceMap1732swap=true := by decide +kernel
theorem fusedMap1732swap_checked : acceptsGraphIso
    (fused (graph core1732) (root 9) 1 0) DegreeOneSmallSpectrum1558.graph fusedMap1732swap=true := by decide +kernel
theorem certified1732swap : Certified (graph core1732) (root 9) 1 0 :=
  of_native_maps core1732 DegreeOneSmallSpectrum1557.graph DegreeOneSmallSpectrum1558.graph
    sourceMap1732swap fusedMap1732swap sourceMap1732swap_checked fusedMap1732swap_checked
    DegreeOneSmallComparisons.comparison1732
#print axioms sourceMap1732swap_checked
#print axioms fusedMap1732swap_checked
#print axioms certified1732swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

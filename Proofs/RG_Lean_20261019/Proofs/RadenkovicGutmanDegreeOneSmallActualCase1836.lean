/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1836 : Family 10 := level10.get ⟨87,by decide⟩
def sourceMap1836 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1836 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1836_checked : acceptsGraphIso
    (source (graph core1836) (root 10) 0 0) DegreeOneSmallSpectrum1253.graph sourceMap1836=true := by decide +kernel
theorem fusedMap1836_checked : acceptsGraphIso
    (fused (graph core1836) (root 10) 0 0) DegreeOneSmallSpectrum909.graph fusedMap1836=true := by decide +kernel
theorem certified1836 : Certified (graph core1836) (root 10) 0 0 :=
  of_native_maps core1836 DegreeOneSmallSpectrum1253.graph DegreeOneSmallSpectrum909.graph
    sourceMap1836 fusedMap1836 sourceMap1836_checked fusedMap1836_checked
    DegreeOneSmallComparisons.comparison1836
#print axioms sourceMap1836_checked
#print axioms fusedMap1836_checked
#print axioms certified1836
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

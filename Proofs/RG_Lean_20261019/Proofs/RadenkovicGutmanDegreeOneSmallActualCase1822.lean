/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1822 : Family 10 := level10.get ⟨67,by decide⟩
def sourceMap1822 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1822 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1822_checked : acceptsGraphIso
    (source (graph core1822) (root 10) 0 0) DegreeOneSmallSpectrum1203.graph sourceMap1822=true := by decide +kernel
theorem fusedMap1822_checked : acceptsGraphIso
    (fused (graph core1822) (root 10) 0 0) DegreeOneSmallSpectrum880.graph fusedMap1822=true := by decide +kernel
theorem certified1822 : Certified (graph core1822) (root 10) 0 0 :=
  of_native_maps core1822 DegreeOneSmallSpectrum1203.graph DegreeOneSmallSpectrum880.graph
    sourceMap1822 fusedMap1822 sourceMap1822_checked fusedMap1822_checked
    DegreeOneSmallComparisons.comparison1822
#print axioms sourceMap1822_checked
#print axioms fusedMap1822_checked
#print axioms certified1822
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1111 : Family 8 := level8.get ⟨161,by decide⟩
def sourceMap1111 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap1111 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap1111_checked : acceptsGraphIso
    (source (graph core1111) (root 8) 0 0) DegreeOneSmallSpectrum347.graph sourceMap1111=true := by decide +kernel
theorem fusedMap1111_checked : acceptsGraphIso
    (fused (graph core1111) (root 8) 0 0) DegreeOneSmallSpectrum345.graph fusedMap1111=true := by decide +kernel
theorem certified1111 : Certified (graph core1111) (root 8) 0 0 :=
  of_native_maps core1111 DegreeOneSmallSpectrum347.graph DegreeOneSmallSpectrum345.graph
    sourceMap1111 fusedMap1111 sourceMap1111_checked fusedMap1111_checked
    DegreeOneSmallComparisons.comparison1111
#print axioms sourceMap1111_checked
#print axioms fusedMap1111_checked
#print axioms certified1111
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

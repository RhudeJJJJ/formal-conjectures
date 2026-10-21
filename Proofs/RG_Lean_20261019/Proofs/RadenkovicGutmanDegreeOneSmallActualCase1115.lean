/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1115 : Family 8 := level8.get ⟨163,by decide⟩
def sourceMap1115 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,8,9,10,1,2,3,4,6,7] (sourceLabel 8 0 0 v)
def fusedMap1115 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap1115_checked : acceptsGraphIso
    (source (graph core1115) (root 8) 0 0) DegreeOneSmallSpectrum245.graph sourceMap1115=true := by decide +kernel
theorem fusedMap1115_checked : acceptsGraphIso
    (fused (graph core1115) (root 8) 0 0) DegreeOneSmallSpectrum346.graph fusedMap1115=true := by decide +kernel
theorem certified1115 : Certified (graph core1115) (root 8) 0 0 :=
  of_native_maps core1115 DegreeOneSmallSpectrum245.graph DegreeOneSmallSpectrum346.graph
    sourceMap1115 fusedMap1115 sourceMap1115_checked fusedMap1115_checked
    DegreeOneSmallComparisons.comparison1115
#print axioms sourceMap1115_checked
#print axioms fusedMap1115_checked
#print axioms certified1115
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

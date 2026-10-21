/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1011 : Family 8 := level8.get ⟨104,by decide⟩
def sourceMap1011 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,9,10,7,8] (sourceLabel 8 0 0 v)
def fusedMap1011 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1011_checked : acceptsGraphIso
    (source (graph core1011) (root 8) 0 0) DegreeOneSmallSpectrum260.graph sourceMap1011=true := by decide +kernel
theorem fusedMap1011_checked : acceptsGraphIso
    (fused (graph core1011) (root 8) 0 0) DegreeOneSmallSpectrum266.graph fusedMap1011=true := by decide +kernel
theorem certified1011 : Certified (graph core1011) (root 8) 0 0 :=
  of_native_maps core1011 DegreeOneSmallSpectrum260.graph DegreeOneSmallSpectrum266.graph
    sourceMap1011 fusedMap1011 sourceMap1011_checked fusedMap1011_checked
    DegreeOneSmallComparisons.comparison1011
#print axioms sourceMap1011_checked
#print axioms fusedMap1011_checked
#print axioms certified1011
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

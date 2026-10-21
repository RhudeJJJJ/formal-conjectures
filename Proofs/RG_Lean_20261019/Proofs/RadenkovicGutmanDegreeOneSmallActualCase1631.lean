/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1631 : Family 9 := level9.get ⟨374,by decide⟩
def sourceMap1631 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1631 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1631_checked : acceptsGraphIso
    (source (graph core1631) (root 9) 0 0) DegreeOneSmallSpectrum742.graph sourceMap1631=true := by decide +kernel
theorem fusedMap1631_checked : acceptsGraphIso
    (fused (graph core1631) (root 9) 0 0) DegreeOneSmallSpectrum741.graph fusedMap1631=true := by decide +kernel
theorem certified1631 : Certified (graph core1631) (root 9) 0 0 :=
  of_native_maps core1631 DegreeOneSmallSpectrum742.graph DegreeOneSmallSpectrum741.graph
    sourceMap1631 fusedMap1631 sourceMap1631_checked fusedMap1631_checked
    DegreeOneSmallComparisons.comparison1631
#print axioms sourceMap1631_checked
#print axioms fusedMap1631_checked
#print axioms certified1631
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

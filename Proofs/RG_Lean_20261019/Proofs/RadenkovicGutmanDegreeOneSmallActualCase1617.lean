/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1617 : Family 9 := level9.get ⟨359,by decide⟩
def sourceMap1617 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1617 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1617_checked : acceptsGraphIso
    (source (graph core1617) (root 9) 0 0) DegreeOneSmallSpectrum692.graph sourceMap1617=true := by decide +kernel
theorem fusedMap1617_checked : acceptsGraphIso
    (fused (graph core1617) (root 9) 0 0) DegreeOneSmallSpectrum697.graph fusedMap1617=true := by decide +kernel
theorem certified1617 : Certified (graph core1617) (root 9) 0 0 :=
  of_native_maps core1617 DegreeOneSmallSpectrum692.graph DegreeOneSmallSpectrum697.graph
    sourceMap1617 fusedMap1617 sourceMap1617_checked fusedMap1617_checked
    DegreeOneSmallComparisons.comparison1617
#print axioms sourceMap1617_checked
#print axioms fusedMap1617_checked
#print axioms certified1617
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1525 : Family 9 := level9.get ⟨256,by decide⟩
def sourceMap1525 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1525 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1525_checked : acceptsGraphIso
    (source (graph core1525) (root 9) 0 0) DegreeOneSmallSpectrum742.graph sourceMap1525=true := by decide +kernel
theorem fusedMap1525_checked : acceptsGraphIso
    (fused (graph core1525) (root 9) 0 0) DegreeOneSmallSpectrum566.graph fusedMap1525=true := by decide +kernel
theorem certified1525 : Certified (graph core1525) (root 9) 0 0 :=
  of_native_maps core1525 DegreeOneSmallSpectrum742.graph DegreeOneSmallSpectrum566.graph
    sourceMap1525 fusedMap1525 sourceMap1525_checked fusedMap1525_checked
    DegreeOneSmallComparisons.comparison1525
#print axioms sourceMap1525_checked
#print axioms fusedMap1525_checked
#print axioms certified1525
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

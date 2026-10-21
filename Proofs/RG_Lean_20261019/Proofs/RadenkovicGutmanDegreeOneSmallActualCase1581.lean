/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1581 : Family 9 := level9.get ⟨323,by decide⟩
def sourceMap1581 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1581 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1581_checked : acceptsGraphIso
    (source (graph core1581) (root 9) 0 0) DegreeOneSmallSpectrum613.graph sourceMap1581=true := by decide +kernel
theorem fusedMap1581_checked : acceptsGraphIso
    (fused (graph core1581) (root 9) 0 0) DegreeOneSmallSpectrum617.graph fusedMap1581=true := by decide +kernel
theorem certified1581 : Certified (graph core1581) (root 9) 0 0 :=
  of_native_maps core1581 DegreeOneSmallSpectrum613.graph DegreeOneSmallSpectrum617.graph
    sourceMap1581 fusedMap1581 sourceMap1581_checked fusedMap1581_checked
    DegreeOneSmallComparisons.comparison1581
#print axioms sourceMap1581_checked
#print axioms fusedMap1581_checked
#print axioms certified1581
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

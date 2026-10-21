/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1399 : Family 9 := level9.get ⟨145,by decide⟩
def sourceMap1399 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1399 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1399_checked : acceptsGraphIso
    (source (graph core1399) (root 9) 0 0) DegreeOneSmallSpectrum652.graph sourceMap1399=true := by decide +kernel
theorem fusedMap1399_checked : acceptsGraphIso
    (fused (graph core1399) (root 9) 0 0) DegreeOneSmallSpectrum410.graph fusedMap1399=true := by decide +kernel
theorem certified1399 : Certified (graph core1399) (root 9) 0 0 :=
  of_native_maps core1399 DegreeOneSmallSpectrum652.graph DegreeOneSmallSpectrum410.graph
    sourceMap1399 fusedMap1399 sourceMap1399_checked fusedMap1399_checked
    DegreeOneSmallComparisons.comparison1399
#print axioms sourceMap1399_checked
#print axioms fusedMap1399_checked
#print axioms certified1399
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

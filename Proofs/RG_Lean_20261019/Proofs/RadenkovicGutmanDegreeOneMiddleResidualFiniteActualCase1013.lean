/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1013 : Family 10 := level10.get ⟨929,by decide⟩
def sourceMap1013 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1013 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1013_checked : acceptsGraphIso
    (source (graph core1013) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2316.graph sourceMap1013=true := by decide +kernel
theorem fusedMap1013_checked : acceptsGraphIso
    (fused (graph core1013) (root 10) 2 2) DegreeTwoThreeSpectrum5823.graph fusedMap1013=true := by decide +kernel
theorem certified1013 : Certified (graph core1013) (root 10) 2 2 :=
  of_native_maps core1013 DegreeOneMiddleResidualSpectrum2316.graph DegreeTwoThreeSpectrum5823.graph
    sourceMap1013 fusedMap1013 sourceMap1013_checked fusedMap1013_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1013
#print axioms sourceMap1013_checked
#print axioms fusedMap1013_checked
#print axioms certified1013
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

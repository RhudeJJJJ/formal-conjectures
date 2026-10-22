/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1006 : Family 10 := level10.get ⟨901,by decide⟩
def sourceMap1006 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1006 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1006_checked : acceptsGraphIso
    (source (graph core1006) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2309.graph sourceMap1006=true := by decide +kernel
theorem fusedMap1006_checked : acceptsGraphIso
    (fused (graph core1006) (root 10) 2 2) DegreeTwoThreeSpectrum5767.graph fusedMap1006=true := by decide +kernel
theorem certified1006 : Certified (graph core1006) (root 10) 2 2 :=
  of_native_maps core1006 DegreeOneMiddleResidualSpectrum2309.graph DegreeTwoThreeSpectrum5767.graph
    sourceMap1006 fusedMap1006 sourceMap1006_checked fusedMap1006_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1006
#print axioms sourceMap1006_checked
#print axioms fusedMap1006_checked
#print axioms certified1006
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

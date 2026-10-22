/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1135 : Family 10 := level10.get ⟨1300,by decide⟩
def sourceMap1135 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1135 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1135_checked : acceptsGraphIso
    (source (graph core1135) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2188.graph sourceMap1135=true := by decide +kernel
theorem fusedMap1135_checked : acceptsGraphIso
    (fused (graph core1135) (root 10) 2 2) DegreeTwoThreeSpectrum6589.graph fusedMap1135=true := by decide +kernel
theorem certified1135 : Certified (graph core1135) (root 10) 2 2 :=
  of_native_maps core1135 DegreeOneMiddleResidualSpectrum2188.graph DegreeTwoThreeSpectrum6589.graph
    sourceMap1135 fusedMap1135 sourceMap1135_checked fusedMap1135_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1135
#print axioms sourceMap1135_checked
#print axioms fusedMap1135_checked
#print axioms certified1135
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

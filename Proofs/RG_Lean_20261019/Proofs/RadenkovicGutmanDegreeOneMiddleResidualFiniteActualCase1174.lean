/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1174 : Family 10 := level10.get ⟨1524,by decide⟩
def sourceMap1174 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1174 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1174_checked : acceptsGraphIso
    (source (graph core1174) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2330.graph sourceMap1174=true := by decide +kernel
theorem fusedMap1174_checked : acceptsGraphIso
    (fused (graph core1174) (root 10) 2 2) DegreeTwoThreeSpectrum5960.graph fusedMap1174=true := by decide +kernel
theorem certified1174 : Certified (graph core1174) (root 10) 2 2 :=
  of_native_maps core1174 DegreeOneMiddleResidualSpectrum2330.graph DegreeTwoThreeSpectrum5960.graph
    sourceMap1174 fusedMap1174 sourceMap1174_checked fusedMap1174_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1174
#print axioms sourceMap1174_checked
#print axioms fusedMap1174_checked
#print axioms certified1174
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

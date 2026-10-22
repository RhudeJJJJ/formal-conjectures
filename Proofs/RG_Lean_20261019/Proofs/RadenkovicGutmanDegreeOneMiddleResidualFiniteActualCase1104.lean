/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1104 : Family 10 := level10.get ⟨1181,by decide⟩
def sourceMap1104 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1104 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1104_checked : acceptsGraphIso
    (source (graph core1104) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2106.graph sourceMap1104=true := by decide +kernel
theorem fusedMap1104_checked : acceptsGraphIso
    (fused (graph core1104) (root 10) 2 2) DegreeTwoThreeSpectrum6349.graph fusedMap1104=true := by decide +kernel
theorem certified1104 : Certified (graph core1104) (root 10) 2 2 :=
  of_native_maps core1104 DegreeOneMiddleResidualSpectrum2106.graph DegreeTwoThreeSpectrum6349.graph
    sourceMap1104 fusedMap1104 sourceMap1104_checked fusedMap1104_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1104
#print axioms sourceMap1104_checked
#print axioms fusedMap1104_checked
#print axioms certified1104
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

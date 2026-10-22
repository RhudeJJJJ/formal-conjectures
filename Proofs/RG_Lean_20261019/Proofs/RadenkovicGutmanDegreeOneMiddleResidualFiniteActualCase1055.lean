/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1055 : Family 10 := level10.get ⟨1048,by decide⟩
def sourceMap1055 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1055 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1055_checked : acceptsGraphIso
    (source (graph core1055) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2004.graph sourceMap1055=true := by decide +kernel
theorem fusedMap1055_checked : acceptsGraphIso
    (fused (graph core1055) (root 10) 2 2) DegreeTwoThreeSpectrum6082.graph fusedMap1055=true := by decide +kernel
theorem certified1055 : Certified (graph core1055) (root 10) 2 2 :=
  of_native_maps core1055 DegreeOneMiddleResidualSpectrum2004.graph DegreeTwoThreeSpectrum6082.graph
    sourceMap1055 fusedMap1055 sourceMap1055_checked fusedMap1055_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1055
#print axioms sourceMap1055_checked
#print axioms fusedMap1055_checked
#print axioms certified1055
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

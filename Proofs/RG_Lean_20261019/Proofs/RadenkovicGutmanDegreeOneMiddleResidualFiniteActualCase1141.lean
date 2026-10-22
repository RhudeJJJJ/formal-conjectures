/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1141 : Family 10 := level10.get ⟨1317,by decide⟩
def sourceMap1141 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1141 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1141_checked : acceptsGraphIso
    (source (graph core1141) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2201.graph sourceMap1141=true := by decide +kernel
theorem fusedMap1141_checked : acceptsGraphIso
    (fused (graph core1141) (root 10) 2 2) DegreeTwoThreeSpectrum6622.graph fusedMap1141=true := by decide +kernel
theorem certified1141 : Certified (graph core1141) (root 10) 2 2 :=
  of_native_maps core1141 DegreeOneMiddleResidualSpectrum2201.graph DegreeTwoThreeSpectrum6622.graph
    sourceMap1141 fusedMap1141 sourceMap1141_checked fusedMap1141_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1141
#print axioms sourceMap1141_checked
#print axioms fusedMap1141_checked
#print axioms certified1141
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

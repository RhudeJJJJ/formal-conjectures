/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1058 : Family 10 := level10.get ⟨1054,by decide⟩
def sourceMap1058 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1058 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1058_checked : acceptsGraphIso
    (source (graph core1058) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2009.graph sourceMap1058=true := by decide +kernel
theorem fusedMap1058_checked : acceptsGraphIso
    (fused (graph core1058) (root 10) 2 2) DegreeTwoThreeSpectrum6096.graph fusedMap1058=true := by decide +kernel
theorem certified1058 : Certified (graph core1058) (root 10) 2 2 :=
  of_native_maps core1058 DegreeOneMiddleResidualSpectrum2009.graph DegreeTwoThreeSpectrum6096.graph
    sourceMap1058 fusedMap1058 sourceMap1058_checked fusedMap1058_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1058
#print axioms sourceMap1058_checked
#print axioms fusedMap1058_checked
#print axioms certified1058
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

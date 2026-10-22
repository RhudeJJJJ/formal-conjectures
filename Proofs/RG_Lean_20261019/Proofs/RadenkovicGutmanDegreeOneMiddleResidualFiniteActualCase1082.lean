/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1082 : Family 10 := level10.get ⟨1116,by decide⟩
def sourceMap1082 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1082 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1082_checked : acceptsGraphIso
    (source (graph core1082) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2057.graph sourceMap1082=true := by decide +kernel
theorem fusedMap1082_checked : acceptsGraphIso
    (fused (graph core1082) (root 10) 2 2) DegreeTwoThreeSpectrum6220.graph fusedMap1082=true := by decide +kernel
theorem certified1082 : Certified (graph core1082) (root 10) 2 2 :=
  of_native_maps core1082 DegreeOneMiddleResidualSpectrum2057.graph DegreeTwoThreeSpectrum6220.graph
    sourceMap1082 fusedMap1082 sourceMap1082_checked fusedMap1082_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1082
#print axioms sourceMap1082_checked
#print axioms fusedMap1082_checked
#print axioms certified1082
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

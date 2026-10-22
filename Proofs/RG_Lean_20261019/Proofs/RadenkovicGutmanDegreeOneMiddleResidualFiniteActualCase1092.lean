/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1092 : Family 10 := level10.get ⟨1146,by decide⟩
def sourceMap1092 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1092 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1092_checked : acceptsGraphIso
    (source (graph core1092) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2080.graph sourceMap1092=true := by decide +kernel
theorem fusedMap1092_checked : acceptsGraphIso
    (fused (graph core1092) (root 10) 2 2) DegreeTwoThreeSpectrum6280.graph fusedMap1092=true := by decide +kernel
theorem certified1092 : Certified (graph core1092) (root 10) 2 2 :=
  of_native_maps core1092 DegreeOneMiddleResidualSpectrum2080.graph DegreeTwoThreeSpectrum6280.graph
    sourceMap1092 fusedMap1092 sourceMap1092_checked fusedMap1092_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1092
#print axioms sourceMap1092_checked
#print axioms fusedMap1092_checked
#print axioms certified1092
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

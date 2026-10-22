/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1179 : Family 10 := level10.get ⟨1534,by decide⟩
def sourceMap1179 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1179 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1179_checked : acceptsGraphIso
    (source (graph core1179) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2335.graph sourceMap1179=true := by decide +kernel
theorem fusedMap1179_checked : acceptsGraphIso
    (fused (graph core1179) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1517.graph fusedMap1179=true := by decide +kernel
theorem certified1179 : Certified (graph core1179) (root 10) 2 2 :=
  of_native_maps core1179 DegreeOneMiddleResidualSpectrum2335.graph DegreeOneMiddleResidualSpectrum1517.graph
    sourceMap1179 fusedMap1179 sourceMap1179_checked fusedMap1179_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1179
#print axioms sourceMap1179_checked
#print axioms fusedMap1179_checked
#print axioms certified1179
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

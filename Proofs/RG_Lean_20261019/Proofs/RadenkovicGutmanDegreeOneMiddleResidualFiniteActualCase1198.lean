/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1198 : Family 10 := level10.get ⟨1699,by decide⟩
def sourceMap1198 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1198 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1198_checked : acceptsGraphIso
    (source (graph core1198) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2354.graph sourceMap1198=true := by decide +kernel
theorem fusedMap1198_checked : acceptsGraphIso
    (fused (graph core1198) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1707.graph fusedMap1198=true := by decide +kernel
theorem certified1198 : Certified (graph core1198) (root 10) 2 2 :=
  of_native_maps core1198 DegreeOneMiddleResidualSpectrum2354.graph DegreeOneMiddleResidualSpectrum1707.graph
    sourceMap1198 fusedMap1198 sourceMap1198_checked fusedMap1198_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1198
#print axioms sourceMap1198_checked
#print axioms fusedMap1198_checked
#print axioms certified1198
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1068 : Family 10 := level10.get ⟨1077,by decide⟩
def sourceMap1068 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1068 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1068_checked : acceptsGraphIso
    (source (graph core1068) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2028.graph sourceMap1068=true := by decide +kernel
theorem fusedMap1068_checked : acceptsGraphIso
    (fused (graph core1068) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1580.graph fusedMap1068=true := by decide +kernel
theorem certified1068 : Certified (graph core1068) (root 10) 2 2 :=
  of_native_maps core1068 DegreeOneMiddleResidualSpectrum2028.graph DegreeOneMiddleResidualSpectrum1580.graph
    sourceMap1068 fusedMap1068 sourceMap1068_checked fusedMap1068_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1068
#print axioms sourceMap1068_checked
#print axioms fusedMap1068_checked
#print axioms certified1068
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

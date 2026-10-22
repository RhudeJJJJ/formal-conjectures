/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1083 : Family 10 := level10.get ⟨1118,by decide⟩
def sourceMap1083 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1083 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1083_checked : acceptsGraphIso
    (source (graph core1083) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2059.graph sourceMap1083=true := by decide +kernel
theorem fusedMap1083_checked : acceptsGraphIso
    (fused (graph core1083) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1615.graph fusedMap1083=true := by decide +kernel
theorem certified1083 : Certified (graph core1083) (root 10) 2 2 :=
  of_native_maps core1083 DegreeOneMiddleResidualSpectrum2059.graph DegreeOneMiddleResidualSpectrum1615.graph
    sourceMap1083 fusedMap1083 sourceMap1083_checked fusedMap1083_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1083
#print axioms sourceMap1083_checked
#print axioms fusedMap1083_checked
#print axioms certified1083
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

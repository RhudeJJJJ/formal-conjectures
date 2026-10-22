/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1097 : Family 10 := level10.get ⟨1153,by decide⟩
def sourceMap1097 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1097 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1097_checked : acceptsGraphIso
    (source (graph core1097) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2087.graph sourceMap1097=true := by decide +kernel
theorem fusedMap1097_checked : acceptsGraphIso
    (fused (graph core1097) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1639.graph fusedMap1097=true := by decide +kernel
theorem certified1097 : Certified (graph core1097) (root 10) 2 2 :=
  of_native_maps core1097 DegreeOneMiddleResidualSpectrum2087.graph DegreeOneMiddleResidualSpectrum1639.graph
    sourceMap1097 fusedMap1097 sourceMap1097_checked fusedMap1097_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1097
#print axioms sourceMap1097_checked
#print axioms fusedMap1097_checked
#print axioms certified1097
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

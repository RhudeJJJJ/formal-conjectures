/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1109 : Family 10 := level10.get ⟨1190,by decide⟩
def sourceMap1109 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1109 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1109_checked : acceptsGraphIso
    (source (graph core1109) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2114.graph sourceMap1109=true := by decide +kernel
theorem fusedMap1109_checked : acceptsGraphIso
    (fused (graph core1109) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1665.graph fusedMap1109=true := by decide +kernel
theorem certified1109 : Certified (graph core1109) (root 10) 2 2 :=
  of_native_maps core1109 DegreeOneMiddleResidualSpectrum2114.graph DegreeOneMiddleResidualSpectrum1665.graph
    sourceMap1109 fusedMap1109 sourceMap1109_checked fusedMap1109_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1109
#print axioms sourceMap1109_checked
#print axioms fusedMap1109_checked
#print axioms certified1109
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

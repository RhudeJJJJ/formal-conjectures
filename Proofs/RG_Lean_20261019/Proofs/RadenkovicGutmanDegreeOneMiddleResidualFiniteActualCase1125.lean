/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1125 : Family 10 := level10.get ⟨1261,by decide⟩
def sourceMap1125 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1125 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1125_checked : acceptsGraphIso
    (source (graph core1125) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2161.graph sourceMap1125=true := by decide +kernel
theorem fusedMap1125_checked : acceptsGraphIso
    (fused (graph core1125) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1724.graph fusedMap1125=true := by decide +kernel
theorem certified1125 : Certified (graph core1125) (root 10) 2 2 :=
  of_native_maps core1125 DegreeOneMiddleResidualSpectrum2161.graph DegreeOneMiddleResidualSpectrum1724.graph
    sourceMap1125 fusedMap1125 sourceMap1125_checked fusedMap1125_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1125
#print axioms sourceMap1125_checked
#print axioms fusedMap1125_checked
#print axioms certified1125
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

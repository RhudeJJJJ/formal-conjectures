/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1140 : Family 10 := level10.get ⟨1309,by decide⟩
def sourceMap1140 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1140 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1140_checked : acceptsGraphIso
    (source (graph core1140) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2196.graph sourceMap1140=true := by decide +kernel
theorem fusedMap1140_checked : acceptsGraphIso
    (fused (graph core1140) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1758.graph fusedMap1140=true := by decide +kernel
theorem certified1140 : Certified (graph core1140) (root 10) 2 2 :=
  of_native_maps core1140 DegreeOneMiddleResidualSpectrum2196.graph DegreeOneMiddleResidualSpectrum1758.graph
    sourceMap1140 fusedMap1140 sourceMap1140_checked fusedMap1140_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1140
#print axioms sourceMap1140_checked
#print axioms fusedMap1140_checked
#print axioms certified1140
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

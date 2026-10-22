/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1197 : Family 10 := level10.get ⟨1646,by decide⟩
def sourceMap1197 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1197 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1197_checked : acceptsGraphIso
    (source (graph core1197) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2353.graph sourceMap1197=true := by decide +kernel
theorem fusedMap1197_checked : acceptsGraphIso
    (fused (graph core1197) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1620.graph fusedMap1197=true := by decide +kernel
theorem certified1197 : Certified (graph core1197) (root 10) 2 2 :=
  of_native_maps core1197 DegreeOneMiddleResidualSpectrum2353.graph DegreeOneMiddleResidualSpectrum1620.graph
    sourceMap1197 fusedMap1197 sourceMap1197_checked fusedMap1197_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1197
#print axioms sourceMap1197_checked
#print axioms fusedMap1197_checked
#print axioms certified1197
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

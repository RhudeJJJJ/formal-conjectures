/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1190 : Family 10 := level10.get ⟨1583,by decide⟩
def sourceMap1190 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1190 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1190_checked : acceptsGraphIso
    (source (graph core1190) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2346.graph sourceMap1190=true := by decide +kernel
theorem fusedMap1190_checked : acceptsGraphIso
    (fused (graph core1190) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1558.graph fusedMap1190=true := by decide +kernel
theorem certified1190 : Certified (graph core1190) (root 10) 2 2 :=
  of_native_maps core1190 DegreeOneMiddleResidualSpectrum2346.graph DegreeOneMiddleResidualSpectrum1558.graph
    sourceMap1190 fusedMap1190 sourceMap1190_checked fusedMap1190_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1190
#print axioms sourceMap1190_checked
#print axioms fusedMap1190_checked
#print axioms certified1190
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

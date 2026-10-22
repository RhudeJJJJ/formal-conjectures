/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1187 : Family 10 := level10.get ⟨1569,by decide⟩
def sourceMap1187 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1187 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1187_checked : acceptsGraphIso
    (source (graph core1187) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2343.graph sourceMap1187=true := by decide +kernel
theorem fusedMap1187_checked : acceptsGraphIso
    (fused (graph core1187) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1547.graph fusedMap1187=true := by decide +kernel
theorem certified1187 : Certified (graph core1187) (root 10) 2 2 :=
  of_native_maps core1187 DegreeOneMiddleResidualSpectrum2343.graph DegreeOneMiddleResidualSpectrum1547.graph
    sourceMap1187 fusedMap1187 sourceMap1187_checked fusedMap1187_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1187
#print axioms sourceMap1187_checked
#print axioms fusedMap1187_checked
#print axioms certified1187
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

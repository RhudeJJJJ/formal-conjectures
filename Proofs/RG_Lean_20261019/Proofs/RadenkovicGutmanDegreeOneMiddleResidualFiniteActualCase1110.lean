/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1110 : Family 10 := level10.get ⟨1194,by decide⟩
def sourceMap1110 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1110 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1110_checked : acceptsGraphIso
    (source (graph core1110) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2117.graph sourceMap1110=true := by decide +kernel
theorem fusedMap1110_checked : acceptsGraphIso
    (fused (graph core1110) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1667.graph fusedMap1110=true := by decide +kernel
theorem certified1110 : Certified (graph core1110) (root 10) 2 2 :=
  of_native_maps core1110 DegreeOneMiddleResidualSpectrum2117.graph DegreeOneMiddleResidualSpectrum1667.graph
    sourceMap1110 fusedMap1110 sourceMap1110_checked fusedMap1110_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1110
#print axioms sourceMap1110_checked
#print axioms fusedMap1110_checked
#print axioms certified1110
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

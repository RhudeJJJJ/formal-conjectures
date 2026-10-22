/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1130 : Family 10 := level10.get ⟨1275,by decide⟩
def sourceMap1130 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1130 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1130_checked : acceptsGraphIso
    (source (graph core1130) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2172.graph sourceMap1130=true := by decide +kernel
theorem fusedMap1130_checked : acceptsGraphIso
    (fused (graph core1130) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1733.graph fusedMap1130=true := by decide +kernel
theorem certified1130 : Certified (graph core1130) (root 10) 2 2 :=
  of_native_maps core1130 DegreeOneMiddleResidualSpectrum2172.graph DegreeOneMiddleResidualSpectrum1733.graph
    sourceMap1130 fusedMap1130 sourceMap1130_checked fusedMap1130_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1130
#print axioms sourceMap1130_checked
#print axioms fusedMap1130_checked
#print axioms certified1130
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

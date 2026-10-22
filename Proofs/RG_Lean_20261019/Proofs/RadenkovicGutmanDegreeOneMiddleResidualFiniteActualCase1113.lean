/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1113 : Family 10 := level10.get ⟨1240,by decide⟩
def sourceMap1113 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1113 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1113_checked : acceptsGraphIso
    (source (graph core1113) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2142.graph sourceMap1113=true := by decide +kernel
theorem fusedMap1113_checked : acceptsGraphIso
    (fused (graph core1113) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1708.graph fusedMap1113=true := by decide +kernel
theorem certified1113 : Certified (graph core1113) (root 10) 2 2 :=
  of_native_maps core1113 DegreeOneMiddleResidualSpectrum2142.graph DegreeOneMiddleResidualSpectrum1708.graph
    sourceMap1113 fusedMap1113 sourceMap1113_checked fusedMap1113_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1113
#print axioms sourceMap1113_checked
#print axioms fusedMap1113_checked
#print axioms certified1113
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

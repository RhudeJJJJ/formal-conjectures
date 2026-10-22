/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1114 : Family 10 := level10.get ⟨1241,by decide⟩
def sourceMap1114 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1114 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1114_checked : acceptsGraphIso
    (source (graph core1114) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2143.graph sourceMap1114=true := by decide +kernel
theorem fusedMap1114_checked : acceptsGraphIso
    (fused (graph core1114) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1710.graph fusedMap1114=true := by decide +kernel
theorem certified1114 : Certified (graph core1114) (root 10) 2 2 :=
  of_native_maps core1114 DegreeOneMiddleResidualSpectrum2143.graph DegreeOneMiddleResidualSpectrum1710.graph
    sourceMap1114 fusedMap1114 sourceMap1114_checked fusedMap1114_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1114
#print axioms sourceMap1114_checked
#print axioms fusedMap1114_checked
#print axioms certified1114
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

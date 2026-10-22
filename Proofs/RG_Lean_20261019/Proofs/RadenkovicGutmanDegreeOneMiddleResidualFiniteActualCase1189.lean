/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1189 : Family 10 := level10.get ⟨1575,by decide⟩
def sourceMap1189 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1189 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1189_checked : acceptsGraphIso
    (source (graph core1189) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2345.graph sourceMap1189=true := by decide +kernel
theorem fusedMap1189_checked : acceptsGraphIso
    (fused (graph core1189) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1552.graph fusedMap1189=true := by decide +kernel
theorem certified1189 : Certified (graph core1189) (root 10) 2 2 :=
  of_native_maps core1189 DegreeOneMiddleResidualSpectrum2345.graph DegreeOneMiddleResidualSpectrum1552.graph
    sourceMap1189 fusedMap1189 sourceMap1189_checked fusedMap1189_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1189
#print axioms sourceMap1189_checked
#print axioms fusedMap1189_checked
#print axioms certified1189
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

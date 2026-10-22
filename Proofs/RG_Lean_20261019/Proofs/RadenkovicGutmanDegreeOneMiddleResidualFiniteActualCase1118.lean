/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1118 : Family 10 := level10.get ⟨1249,by decide⟩
def sourceMap1118 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1118 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1118_checked : acceptsGraphIso
    (source (graph core1118) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2150.graph sourceMap1118=true := by decide +kernel
theorem fusedMap1118_checked : acceptsGraphIso
    (fused (graph core1118) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1716.graph fusedMap1118=true := by decide +kernel
theorem certified1118 : Certified (graph core1118) (root 10) 2 2 :=
  of_native_maps core1118 DegreeOneMiddleResidualSpectrum2150.graph DegreeOneMiddleResidualSpectrum1716.graph
    sourceMap1118 fusedMap1118 sourceMap1118_checked fusedMap1118_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1118
#print axioms sourceMap1118_checked
#print axioms fusedMap1118_checked
#print axioms certified1118
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

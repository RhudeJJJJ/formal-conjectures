/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1098 : Family 10 := level10.get ⟨1154,by decide⟩
def sourceMap1098 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1098 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1098_checked : acceptsGraphIso
    (source (graph core1098) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2088.graph sourceMap1098=true := by decide +kernel
theorem fusedMap1098_checked : acceptsGraphIso
    (fused (graph core1098) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1640.graph fusedMap1098=true := by decide +kernel
theorem certified1098 : Certified (graph core1098) (root 10) 2 2 :=
  of_native_maps core1098 DegreeOneMiddleResidualSpectrum2088.graph DegreeOneMiddleResidualSpectrum1640.graph
    sourceMap1098 fusedMap1098 sourceMap1098_checked fusedMap1098_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1098
#print axioms sourceMap1098_checked
#print axioms fusedMap1098_checked
#print axioms certified1098
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1186 : Family 10 := level10.get ⟨1568,by decide⟩
def sourceMap1186 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1186 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1186_checked : acceptsGraphIso
    (source (graph core1186) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2342.graph sourceMap1186=true := by decide +kernel
theorem fusedMap1186_checked : acceptsGraphIso
    (fused (graph core1186) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1546.graph fusedMap1186=true := by decide +kernel
theorem certified1186 : Certified (graph core1186) (root 10) 2 2 :=
  of_native_maps core1186 DegreeOneMiddleResidualSpectrum2342.graph DegreeOneMiddleResidualSpectrum1546.graph
    sourceMap1186 fusedMap1186 sourceMap1186_checked fusedMap1186_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1186
#print axioms sourceMap1186_checked
#print axioms fusedMap1186_checked
#print axioms certified1186
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

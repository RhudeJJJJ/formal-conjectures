/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1165 : Family 10 := level10.get ⟨1421,by decide⟩
def sourceMap1165 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1165 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1165_checked : acceptsGraphIso
    (source (graph core1165) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2271.graph sourceMap1165=true := by decide +kernel
theorem fusedMap1165_checked : acceptsGraphIso
    (fused (graph core1165) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1948.graph fusedMap1165=true := by decide +kernel
theorem certified1165 : Certified (graph core1165) (root 10) 2 2 :=
  of_native_maps core1165 DegreeOneMiddleResidualSpectrum2271.graph DegreeOneMiddleResidualSpectrum1948.graph
    sourceMap1165 fusedMap1165 sourceMap1165_checked fusedMap1165_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1165
#print axioms sourceMap1165_checked
#print axioms fusedMap1165_checked
#print axioms certified1165
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

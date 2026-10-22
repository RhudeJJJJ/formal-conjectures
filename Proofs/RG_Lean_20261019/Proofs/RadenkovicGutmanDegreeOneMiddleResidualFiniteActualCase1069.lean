/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1069 : Family 10 := level10.get ⟨1094,by decide⟩
def sourceMap1069 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1069 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1069_checked : acceptsGraphIso
    (source (graph core1069) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2037.graph sourceMap1069=true := by decide +kernel
theorem fusedMap1069_checked : acceptsGraphIso
    (fused (graph core1069) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1595.graph fusedMap1069=true := by decide +kernel
theorem certified1069 : Certified (graph core1069) (root 10) 2 2 :=
  of_native_maps core1069 DegreeOneMiddleResidualSpectrum2037.graph DegreeOneMiddleResidualSpectrum1595.graph
    sourceMap1069 fusedMap1069 sourceMap1069_checked fusedMap1069_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1069
#print axioms sourceMap1069_checked
#print axioms fusedMap1069_checked
#print axioms certified1069
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

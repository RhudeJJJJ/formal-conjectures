/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1018 : Family 10 := level10.get ⟨936,by decide⟩
def sourceMap1018 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1018 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1018_checked : acceptsGraphIso
    (source (graph core1018) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2321.graph sourceMap1018=true := by decide +kernel
theorem fusedMap1018_checked : acceptsGraphIso
    (fused (graph core1018) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1472.graph fusedMap1018=true := by decide +kernel
theorem certified1018 : Certified (graph core1018) (root 10) 2 2 :=
  of_native_maps core1018 DegreeOneMiddleResidualSpectrum2321.graph DegreeOneMiddleResidualSpectrum1472.graph
    sourceMap1018 fusedMap1018 sourceMap1018_checked fusedMap1018_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1018
#print axioms sourceMap1018_checked
#print axioms fusedMap1018_checked
#print axioms certified1018
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
